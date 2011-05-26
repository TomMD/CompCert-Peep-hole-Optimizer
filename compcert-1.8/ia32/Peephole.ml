(* A Peephole optimizer for use in the Compcert framework *)
open Camlcoq
open Datatypes
open Asm

let ml_peephole (f: instruction list) : (instruction list) =
  match f with
  | ((Pmov_rm r1 m1) :: (Pmov_mr m2 r2) :: c :: xs) when r1 == r2 && m1 == m2 ->
	Pmov_rm r1 m1 :: nop :: c :: xs
  | _ -> f
