Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Coq.ZArith.Zbool.

(*
mov r1 (r2);      -- r1 <- mem_0 r2_0
add r2 4;         -- r2 <- r2_0 - 4
sub r2 4;         -- r2 <- r2_0 - 4 + 4
mov (r2) r1;      -- mem <- (r2_0 - 4 + 4, mem_0 r2_0) :: mem_0

=================

mov r1 (r2);      -- r1 <- mem_0 r2 0

mem' == mem
mem_0  == (r2_0 - 4 + 4, mem_0 r2_0) ::  mem_0
mem_0 == (r2_0, mem_0 r2_0) :: mem_0

rs' = rs
r2_0 = - r2_0 - 4 + 4
*)

Inductive Loc : Type :=
  | Register : preg -> Loc
  | Memory   : addrmode -> Loc.

Inductive SymExpr : Type :=
  (* Integers *)
  | add    : SymExpr -> SymExpr -> SymExpr
  | sub    : SymExpr -> SymExpr -> SymExpr
  | mult   : SymExpr -> SymExpr -> SymExpr
  | div_unsigned : SymExpr -> SymExpr -> SymExpr
  | div_signed   : SymExpr -> SymExpr -> SymExpr
  | shiftR : SymExpr -> SymExpr -> SymExpr
  | shiftR_unsigned : SymExpr -> SymExpr -> SymExpr
  | and    : SymExpr -> SymExpr -> SymExpr
  | or     : SymExpr -> SymExpr -> SymExpr
  | neg    : SymExpr -> SymExpr
  | xor    : SymExpr -> SymExpr -> SymExpr
  (* Tests *)
  | cmp    : SymExpr -> SymExpr -> SymExpr
  | test   : SymExpr -> SymExpr -> SymExpr  (* modifies x86 status register! *) 
  (* Floating *)
  | add_f  : SymExpr -> SymExpr -> SymExpr
  | sub_f  : SymExpr -> SymExpr -> SymExpr
  | mult_f : SymExpr -> SymExpr -> SymExpr
  | div_f  : SymExpr -> SymExpr -> SymExpr
  | abs_f  : SymExpr -> SymExpr -> SymExpr
  | neg_f  : SymExpr -> SymExpr -> SymExpr
  | Symbol : Loc -> SymExpr
  | Imm    : val -> SymExpr.

Definition ValMap := Loc -> SymExpr.

Definition symExec (c : code) : ValMap. Admitted.

Definition sameSymbolicExecution (c : code) (d : code) : bool. Admitted.

(** peephole_validate validates the code optimized by the untrusted
  optimizer is semantically correct.  We only need to prove that
  peephole_validate returns true only when the two inputs are
  semantically correct.  It would be nice to have a proof that it
  doesn't return false given certain known-correct conditions, but
  that isn't required.
 *)
Fixpoint peephole_validate (c : Asm.code) (d : Asm.code) : bool :=
  if Zlt_bool (list_length_z c) (list_length_z d)
    then false
    else sameSymbolicExecution (symExec c) (symExec d).

Parameter ml_optimize : Asm.code -> Asm.code.

(** Peephole optimization of function level lists of assembly code. We
  feed the optimizer sliding windows of up to 4 instructions and then
  validate the results returned. If the results are valid, they are
  used, otherwise, they are discarded. **)
Definition opt_window (c : Asm.code) :=
  let c' := ml_optimize c
  in if peephole_validate c c'
      then c'
      else c.

Fixpoint optimize (c : Asm.code) : Asm.code :=
  if zlt (list_length_z c) 4
    then opt_window c
    else match c with
         | i1 :: i2 :: i3 :: i4 :: cs => opt_window (i1 :: i2 :: i3 :: i4 :: nil) ++ (optimize cs)
         | _ => c  (* this isn't right, should fail *)
         end.

Definition transf_function (f: Asm.code) : res Asm.code :=
  OK (optimize f).

Definition transf_fundef (f : Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition peephole_transf_program (p : Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.