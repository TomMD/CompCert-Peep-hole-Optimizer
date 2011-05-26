(* A peephole optimizer for the CompCert framework *)
open Instructions

val ml_optimize : list instruction -> list instruction
