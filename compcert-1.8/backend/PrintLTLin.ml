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

(** Pretty-printer for LTLin code *)

open Format
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open Locations
open Machregsaux
open LTLin
open PrintOp

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"

let reg pp loc =
  match loc with
  | R r ->
      begin match name_of_register r with
      | Some s -> fprintf pp "%s" s
      | None -> fprintf pp "<unknown reg>"
      end
  | S (Local(ofs, ty)) ->
      fprintf pp "local(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)
  | S (Incoming(ofs, ty)) ->
      fprintf pp "incoming(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)
  | S (Outgoing(ofs, ty)) ->
      fprintf pp "outgoing(%s,%ld)" (name_of_type ty) (camlint_of_coqint ofs)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_instruction pp i =
  match i with
  | Lop(op, args, res) ->
      fprintf pp "%a = %a@ "
         reg res (PrintOp.print_operation reg) (op, args)
  | Lload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a]@ "
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
  | Lstore(chunk, addr, args, src) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src
  | Lcall(sg, fn, args, res) ->
      fprintf pp "%a = %a(%a)@ "
        reg res ros fn regs args
  | Ltailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)@ "
        ros fn regs args
  | Lbuiltin(ef, args, res) ->
      fprintf pp "%a = builtin \"%s\"(%a)@ "
        reg res (extern_atom ef.ef_id) regs args
  | Llabel lbl ->
      fprintf pp "%5ld: " (camlint_of_positive lbl)
  | Lgoto lbl ->
      fprintf pp "goto %ld@ " (camlint_of_positive lbl)
  | Lcond(cond, args, lbl) ->
      fprintf pp "if (%a) goto %ld@ "
        (PrintOp.print_condition reg) (cond, args)
        (camlint_of_positive lbl)
  | Ljumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (camlint_of_positive tbl.(i))
      done;
      fprintf pp "@]@ "
  | Lreturn None ->
      fprintf pp "return@ "
  | Lreturn (Some arg) ->
      fprintf pp "return %a@ " reg arg

let print_function pp f =
  fprintf pp "@[<v 2>f(%a) {@ " regs f.fn_params;
  List.iter (print_instruction pp) f.fn_code;
  fprintf pp "@;<0 -2>}@]@."

let print_fundef pp fd =
  match fd with
  | Internal f -> print_function pp f
  | External _ -> ()

let destination : string option ref = ref None
let currpp : formatter option ref = ref None

let print_if fd =
  match !destination with
  | None -> ()
  | Some f ->
      let pp =
        match !currpp with
        | Some pp -> pp
        | None ->
            let oc = open_out f in
            let pp = formatter_of_out_channel oc in
            currpp := Some pp;
            pp
      in print_fundef pp fd
