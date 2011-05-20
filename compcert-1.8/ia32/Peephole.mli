(* A peephole optimizer for the CompCert framework *)
open Instructions

val ml_peephole : list instruction -> list instruction
