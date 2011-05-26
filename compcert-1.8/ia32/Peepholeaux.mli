(* A peephole optimizer for the CompCert framework *)
open Asm

val ml_optimize: (instruction list) -> (instruction list)
