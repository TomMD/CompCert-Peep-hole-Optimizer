(* A peephole optimizer for the CompCert framework *)
open Asm

val ml_optimize: (instruction list) -> (instruction list)
val peephole_failed: (instruction list) -> (instruction list) -> unit
