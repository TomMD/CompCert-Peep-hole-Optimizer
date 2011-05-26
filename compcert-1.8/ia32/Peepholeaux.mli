(* A peephole optimizer for the CompCert framework *)
open Asm

val ml_optimize: (list instruction) -> (list instruction)
