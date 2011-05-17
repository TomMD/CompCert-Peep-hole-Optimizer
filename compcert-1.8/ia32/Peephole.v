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
    else false.  (* TMD Insert real validator here, in the 'else' branch *)

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
