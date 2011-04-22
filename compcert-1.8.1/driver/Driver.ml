(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Clflags

(* Location of the compatibility library *)

let stdlib_path = ref(
  try
    Sys.getenv "COMPCERT_LIBRARY"
  with Not_found ->
    Configuration.stdlib_path)

let command cmd =
  if !option_v then begin
    prerr_string "+ "; prerr_string cmd; prerr_endline ""
  end;
  Sys.command cmd

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

(* Printing of error messages *)

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

(* From C to preprocessed C *)

let preprocess ifile ofile =
  let cmd =
    sprintf "%s -D__COMPCERT__ %s %s %s > %s"
      Configuration.prepro
      (if Configuration.need_stdlib_wrapper
       then sprintf "-I%s" !stdlib_path
       else "")
      (quote_options !prepro_options)
      ifile ofile in
  if command cmd <> 0 then begin
    safe_remove ofile;
    eprintf "Error during preprocessing.\n";
    exit 2
  end

(* From preprocessed C to asm *)

let compile_c_file sourcename ifile ofile =
  Sections.initialize();
  (* Simplification options *)
  let simplifs =
    "b" (* blocks: mandatory *)
  ^ (if !option_fstruct_passing then "s" else "")
  ^ (if !option_fstruct_assign then "S" else "")
  ^ (if !option_fbitfields then "f" else "") in
  (* Parsing and production of a simplified C AST *)
  let ast =
    match Cparser.Parse.preprocessed_file simplifs sourcename ifile with
    | None -> exit 2
    | Some p -> p in
  (* Remove preprocessed file (always a temp file) *)
  safe_remove ifile;
  (* Save C AST if requested *)
  if !option_dparse then begin
    let ofile = Filename.chop_suffix sourcename ".c" ^ ".parsed.c" in
    let oc = open_out ofile in
    Cparser.Cprint.program (Format.formatter_of_out_channel oc) ast;
    close_out oc
  end;
  (* Conversion to Csyntax *)
  let csyntax =
    match C2C.convertProgram ast with
    | None -> exit 2
    | Some p -> p in
  flush stderr;
  (* Prepare to dump Csyntax, Clight, RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (Filename.chop_suffix sourcename ".c" ^ ext)
                   else None in
  set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination_rtl option_drtl ".rtl";
  set_dest PrintRTL.destination_tailcall option_dtailcall ".tailcall.rtl";
  set_dest PrintRTL.destination_castopt option_dcastopt ".castopt.rtl";
  set_dest PrintRTL.destination_constprop option_dconstprop ".constprop.rtl";
  set_dest PrintRTL.destination_cse option_dcse ".cse.rtl";
  set_dest PrintLTLin.destination option_dalloc ".alloc.ltl";
  (* Convert to Asm *)
  let asm =
    match Compiler.transf_c_program csyntax with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Save asm *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

(* From Cminor to asm *)

let compile_cminor_file ifile ofile =
  Sections.initialize();
  let ic = open_in ifile in
  let lb = Lexing.from_channel ic in
  try
    match Compiler.transf_cminor_program
            (CMtypecheck.type_program
              (CMparser.prog CMlexer.token lb)) with
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2
    | Errors.OK p ->
        let oc = open_out ofile in
        PrintAsm.print_program oc p;
        close_out oc
  with Parsing.Parse_error ->
         eprintf "File %s, character %d: Syntax error\n"
                 ifile (Lexing.lexeme_start lb);
         exit 2
     | CMlexer.Error msg ->  
         eprintf "File %s, character %d: %s\n"
                 ifile (Lexing.lexeme_start lb) msg;
         exit 2
     | CMtypecheck.Error msg ->
         eprintf "File %s, type-checking error:\n%s"
                 ifile msg;
         exit 2

(* From asm to object file *)

let assemble ifile ofile =
  let cmd =
    sprintf "%s -o %s %s"
      Configuration.asm ofile ifile in
  let retcode = command cmd in
  if not !option_dasm then safe_remove ifile;
  if retcode <> 0 then begin
    safe_remove ofile;
    eprintf "Error during assembling.\n";
    exit 2
  end

(* Linking *)

let linker exe_name files =
  let cmd =
    sprintf "%s -o %s %s %s"
      Configuration.linker
      (Filename.quote exe_name)
      (quote_options files)
      (if Configuration.need_stdlib_wrapper
       then sprintf "-L%s -lcompcert" !stdlib_path
       else "") in
  if command cmd <> 0 then exit 2

(* Processing of a .c file *)

let process_c_file sourcename =
  let prefixname = Filename.chop_suffix sourcename ".c" in
  if !option_E then begin
    preprocess sourcename (prefixname ^ ".i")
  end else begin
    let preproname = Filename.temp_file "compcert" ".i" in
    preprocess sourcename preproname;
    if !option_S then begin
      compile_c_file sourcename preproname (prefixname ^ ".s")
    end else begin
      let asmname =
        if !option_dasm
        then prefixname ^ ".s"
        else Filename.temp_file "compcert" ".s" in
      compile_c_file sourcename preproname asmname;
      assemble asmname (prefixname ^ ".o")
    end
  end;
  prefixname ^ ".o"

(* Processing of a .cm file *)

let process_cminor_file sourcename =
  let prefixname = Filename.chop_suffix sourcename ".cm" in
  if !option_S then begin
    compile_cminor_file sourcename (prefixname ^ ".s")
  end else begin
    let asmname =
      if !option_dasm
      then prefixname ^ ".s"
      else Filename.temp_file "compcert" ".s" in
    compile_cminor_file sourcename asmname;
    assemble asmname (prefixname ^ ".o")
  end;
  prefixname ^ ".o"

(* Command-line parsing *)

let usage_string =
"ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .cm            Cminor source file
  .o             Object file
  .a             Library file
Processing options:
  -E             Preprocess only, save result in <file>.i
  -S             Compile to assembler only, save result in <file>.s
  -c             Compile to object file only (no linking), result in <file>.o
Preprocessing options:
  -I<dir>        Add <dir> to search path for #include files
  -D<symb>=<val> Define preprocessor symbol
  -U<symb>       Undefine preprocessor symbol
Language support options (use -fno-<opt> to turn off -f<opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flonglong     Partial emulation of 'long long' types [on]
  -fstruct-passing  Emulate passing structs and unions by value [off]
  -fstruct-assign   Emulate assignment between structs or unions [off]
  -fvararg-calls Emulate calls to variable-argument functions [on]
Code generation options:
  -fmadd         Use fused multiply-add and multiply-sub instructions [off]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
Tracing options:
  -dparse        Save C file after parsing and elaboration in <file>.parse.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save unoptimized generated RTL in <file>.rtl
  -dtailcall     Save RTL after tail call optimization in <file>.tailcall.rtl
  -dcastopt      Save RTL after cast optimization in <file>.castopt.rtl
  -dconstprop    Save RTL after constant propagation in <file>.constprop.rtl
  -dcse          Save RTL after CSE optimization in <file>.cse.rtl
  -dalloc        Save LTL after register allocation in <file>.alloc.ltl
  -dasm          Save generated assembly in <file>.s
Linking options:
  -l<lib>        Link library <lib>
  -L<dir>        Add <dir> to search path for libraries
  -o <file>      Generate executable in <file> (default: a.out)
General options:
  -stdlib <dir>  Set the path of the Compcert run-time library [MacOS X only]
  -v             Print external commands before invoking them
"

type action =
  | Set of bool ref
  | Unset of bool ref
  | Self of (string -> unit)
  | String of (string -> unit)
  | Integer of (int -> unit)

let rec find_action s = function
  | [] -> None
  | (re, act) :: rem ->
      if Str.string_match re s 0 then Some act else find_action s rem

let parse_cmdline spec usage =
  let acts = List.map (fun (pat, act) -> (Str.regexp pat, act)) spec in
  let error () =
    eprintf "Usage: %s" usage;
    exit 2 in
  let rec parse i =
    if i < Array.length Sys.argv then begin
      let s = Sys.argv.(i) in
      match find_action s acts with
      | None ->
          if s <> "-help" && s <> "--help" 
          then eprintf "Unknown argument `%s'\n" s;
          error ()
      | Some(Set r) ->
          r := true; parse (i+1)
      | Some(Unset r) ->
          r := false; parse (i+1)
      | Some(Self fn) ->
          fn s; parse (i+1)
      | Some(String fn) ->
          if i + 1 < Array.length Sys.argv then begin
            fn Sys.argv.(i+1); parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; error()
          end
      | Some(Integer fn) ->
          if i + 1 < Array.length Sys.argv then begin
            let n =
              try
                int_of_string Sys.argv.(i+1)
              with Failure _ ->
                eprintf "Argument to option `%s' must be an integer\n" s;
                error()
            in
            fn n; parse (i+2)
          end else begin
            eprintf "Option `%s' expects an argument\n" s; error()
          end
    end
  in parse 1

let cmdline_actions =
  let f_opt name ref =
    ["-f" ^ name ^ "$", Set ref; "-fno-" ^ name ^ "$", Unset ref] in
  [
  "-I$", String(fun s -> prepro_options := s :: "-I" :: !prepro_options);
  "-D$", String(fun s -> prepro_options := s :: "-D" :: !prepro_options);
  "-U$", String(fun s -> prepro_options := s :: "-U" :: !prepro_options);
  "-[IDU].", Self(fun s -> prepro_options := s :: !prepro_options);
  "-[lL].", Self(fun s -> linker_options := s :: !linker_options);
  "-o$", String(fun s -> exe_name := s);
  "-stdlib$", String(fun s -> stdlib_path := s);
  "-dparse$", Set option_dparse;
  "-dc$", Set option_dcmedium;
  "-dclight$", Set option_dclight;
  "-dcminor", Set option_dcminor;
  "-drtl$", Set option_drtl;
  "-dtailcall$", Set option_dtailcall;
  "-dcastopt$", Set option_dcastopt;
  "-dconstprop$", Set option_dconstprop;
  "-dcse$", Set option_dcse;
  "-dalloc$", Set option_dalloc;
  "-dasm$", Set option_dasm;
  "-E$", Set option_E;
  "-S$", Set option_S;
  "-c$", Set option_c;
  "-v$", Set option_v;
  ".*\\.c$", Self (fun s ->
      let objfile = process_c_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.cm$", Self (fun s ->
      let objfile = process_cminor_file s in
      linker_options := objfile :: !linker_options);
  ".*\\.[oa]$", Self (fun s ->
      linker_options := s :: !linker_options);
  "-fsmall-data$", Integer(fun n -> option_small_data := n);
  "-fsmall-const$", Integer(fun n -> option_small_const := n)
  ]
  @ f_opt "longlong" option_flonglong
  @ f_opt "struct-passing" option_fstruct_passing
  @ f_opt "struct-assign" option_fstruct_assign
  @ f_opt "bitfields" option_fbitfields
  @ f_opt "vararg-calls" option_fvararg_calls
  @ f_opt "madd" option_fmadd

let _ =
  Gc.set { (Gc.get()) with Gc.minor_heap_size = 524288 };
  Cparser.Machine.config :=
    begin match Configuration.arch with
    | "powerpc" -> Cparser.Machine.ppc_32_bigendian
    | "arm"     -> Cparser.Machine.arm_littleendian
    | "ia32"    -> Cparser.Machine.x86_32
    | _         -> assert false
    end;
  Cparser.Builtins.set C2C.builtins;
  CPragmas.initialize();
  parse_cmdline cmdline_actions usage_string;
  if !linker_options <> [] 
  && not (!option_c || !option_S || !option_E)
  then begin
    linker !exe_name !linker_options
  end
