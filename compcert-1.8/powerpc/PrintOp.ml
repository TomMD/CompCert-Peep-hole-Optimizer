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

(** Pretty-printing of operators, conditions, addressing modes *)

open Format
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "%a %sf %a" reg r1 (comparison_name c) reg r2
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "%a not(%sf) %a" reg r1 (comparison_name c) reg r2
  | (Cmaskzero n, [r1]) ->
      fprintf pp "%a & 0x%lx == 0" reg r1 (camlint_of_coqint n)
  | (Cmasknotzero n, [r1]) ->
      fprintf pp "%a & 0x%lx != 0" reg r1 (camlint_of_coqint n)
  | _ ->
      fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%F" n
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast8unsigned, [r1] -> fprintf pp "int8unsigned(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Ocast16unsigned, [r1] -> fprintf pp "int16unsigned(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Osubimm n, [r1] -> fprintf pp "%ld - %a" (camlint_of_coqint n) reg r1
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "%a * %ld" reg r1 (camlint_of_coqint n)
  | Odiv, [r1;r2] -> fprintf pp "%a /s %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "%a /u %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Onand, [r1;r2] -> fprintf pp "not(%a & %a)" reg r1 reg r2
  | Onor, [r1;r2] -> fprintf pp "not(%a | %a)" reg r1 reg r2
  | Onxor, [r1;r2] -> fprintf pp "not(%a ^ %a)" reg r1 reg r2
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Orolm(n,m), [r1] ->
      fprintf pp "(%a rol %ld) & 0x%lx"
              reg r1 (camlint_of_coqint n) (camlint_of_coqint m)
  | Onegf, [r1] -> fprintf pp "negf(%a)" reg r1
  | Oabsf, [r1] -> fprintf pp "absf(%a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "%a +f %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "%a -f %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "%a *f %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "%a /f %a" reg r1 reg r2
  | Omuladdf, [r1;r2;r3] -> fprintf pp "%a *f %a +f %a" reg r1 reg r2 reg r3
  | Omulsubf, [r1;r2;r3] -> fprintf pp "%a *f %a -f %a" reg r1 reg r2 reg r3
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ofloatofwords, [r1;r2] -> fprintf pp "floatofwords(%a,%a)" reg r1 reg r2
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Aindexed2, [r1; r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %ld" (extern_atom id) (camlint_of_coqint ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %ld + %a" (extern_atom id) (camlint_of_coqint ofs) reg r1
  | Ainstack ofs, [] -> fprintf pp "stack(%ld)" (camlint_of_coqint ofs)
  | _ -> fprintf pp "<bad addressing>"
