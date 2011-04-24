(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Entry point for the library: parse, elaborate, and transform *)

module CharSet = Set.Make(struct type t = char let compare = compare end)

let transform_program t p =
  let run_pass pass flag p = if CharSet.mem flag t then pass p else p in
  Rename.program
  (run_pass (AddCasts.program ~all:(CharSet.mem 'C' t)) 'c'
  (run_pass (SimplExpr.program ~volatile:(CharSet.mem 'v' t)) 'e'
  (run_pass StructAssign.program 'S'
  (run_pass StructByValue.program 's'
  (run_pass Bitfields.program 'f'
  (run_pass Unblock.program 'b'
  p))))))

let parse_transformations s =
  let t = ref CharSet.empty in
  let set s = String.iter (fun c -> t := CharSet.add c !t) s in
  String.iter
    (function 'b' -> set "b"
            | 'e' -> set "e"
            | 'c' -> set "ec"
            | 'C' -> set "ecC"
            | 's' -> set "s"
            | 'S' -> set "bsS"
            | 'v' -> set "ev"
            | 'f' -> set "bf"
            |  _  -> ())
    s;
  !t

let preprocessed_file transfs name sourcefile =
  Errors.reset();
  let t = parse_transformations transfs in
  let ic = open_in sourcefile in
  let p =
    try
      Rename.program (transform_program t (Elab.elab_preprocessed_file name ic))
    with Parsing.Parse_error ->
           Errors.error "Error during parsing"; []
       | Errors.Abort ->
           [] in
  close_in ic;
  if Errors.check_errors() then None else Some p
