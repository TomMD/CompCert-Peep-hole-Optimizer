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


(* Handling of linker sections *)

type section_name =
  | Section_text
  | Section_data of bool          (* true = init data, false = uninit data *)
  | Section_small_data of bool
  | Section_const
  | Section_small_const
  | Section_string
  | Section_literal
  | Section_jumptable
  | Section_user of string * bool (*writable*) * bool (*executable*)

val initialize: unit -> unit

val define_section:
  string -> ?iname:string -> ?uname:string
         -> ?writable:bool -> ?executable:bool -> ?near:bool -> unit -> unit
val use_section_for: AST.ident -> string -> bool

val define_function: AST.ident -> unit
val define_variable: AST.ident -> int -> bool -> unit
val define_stringlit: AST.ident -> unit

val section_for_variable: AST.ident -> bool -> section_name
val sections_for_function: AST.ident -> section_name * section_name * section_name
val atom_is_small_data: AST.ident -> Integers.Int.int -> bool
