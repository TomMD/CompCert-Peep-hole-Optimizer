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

(* define equality for Loc, used in the Loc store *)
Lemma Loc_eq : forall (x y : Loc), {x = y} +  {x <> y}.
Proof.
  decide equality. apply preg_eq. decide equality; decide equality; try (apply Int.eq_dec). decide equality; try (apply Int.eq_dec). decide equality. decide equality. apply Int.eq_dec. decide equality. decide equality.
Defined.

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

(* here we use a map to store SymExpr in the symbolic execution. This
may not be the right choice because it's not immediately apparent how
to get everything back out of the map -- maybe we need to store a list
of Locs used as keys? *)

Module LocEq.
  Definition t := Loc.
  Definition eq := Loc_eq.
End LocEq.

Module Locmap := EMap(LocEq).

Definition locs := Locmap.t SymExpr.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Locmap.set b c a) (at level 1, b at next level).

(* small step symbolic execution *)
Definition single_symExec (i : instruction) (l : locs) : option locs :=
  match i with
      (** Moves *)
  | Pmov_rr rd r1 =>
      Some (l # (Register rd) <- (l (Register r1)))

  (* | Pmov_ri rd n => *)
  (*     Next (nextinstr (rs#rd <- (Vint n))) m *)
  (* | Pmov_rm rd a => *)
  (*     exec_load Mint32 m a rs rd *)
  (* | Pmov_mr a r1 => *)
  (*     exec_store Mint32 m a rs r1 *)
  (* | Pmovd_fr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (rs r1))) m *)
  (* | Pmovd_rf rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (rs r1))) m *)
  (* | Pmovsd_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (rs r1))) m *)
  (* | Pmovsd_fi rd n => *)
  (*     Next (nextinstr (rs#rd <- (Vfloat n))) m *)
  (* | Pmovsd_fm rd a => *)
  (*     exec_load Mfloat64 m a rs rd *)
  (* | Pmovsd_mf a r1 => *)
  (*     exec_store Mfloat64 m a rs r1 *)
  (* | Pfld_f r1 => *)
  (*     Next (nextinstr (rs#ST0 <- (rs r1))) m *)
  (* | Pfld_m a => *)
  (*     exec_load Mfloat64 m a rs ST0 *)
  (* | Pfstp_f rd => *)
  (*     Next (nextinstr (rs#rd <- (rs ST0))) m *)
  (* | Pfstp_m a => *)
  (*     exec_store Mfloat64 m a rs ST0 *)
  (* (** Moves with conversion *) *)
  (* | Pmovb_mr a r1 => *)
  (*     exec_store Mint8unsigned m a rs r1 *)
  (* | Pmovw_mr a r1 => *)
  (*     exec_store Mint16unsigned m a rs r1 *)
  (* | Pmovzb_rr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m *)
  (* | Pmovzb_rm rd a => *)
  (*     exec_load Mint8unsigned m a rs rd *)
  (* | Pmovsb_rr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m *)
  (* | Pmovsb_rm rd a => *)
  (*     exec_load Mint8signed m a rs rd *)
  (* | Pmovzw_rr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m *)
  (* | Pmovzw_rm rd a => *)
  (*     exec_load Mint16unsigned m a rs rd *)
  (* | Pmovsw_rr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m *)
  (* | Pmovsw_rm rd a => *)
  (*     exec_load Mint16signed m a rs rd *)
  (* | Pcvtss2sd_fm rd a => *)
  (*     exec_load Mfloat32 m a rs rd *)
  (* | Pcvtsd2ss_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m *)
  (* | Pcvtsd2ss_mf a r1 => *)
  (*     exec_store Mfloat32 m a rs r1 *)
  (* | Pcvttsd2si_rf rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.intoffloat rs#r1))) m *)
  (* | Pcvtsi2sd_fr rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.floatofint rs#r1))) m *)
  (* (** Integer arithmetic *) *)
  (* | Plea rd a => *)
  (*     Next (nextinstr (rs#rd <- (eval_addrmode a rs))) m *)
  (* | Pneg rd => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m *)
  (* | Psub_rr rd r1 => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m *)
  (* | Pimul_rr rd r1 => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m *)
  (* | Pimul_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m *)
  (* | Pdiv r1 => *)
  (*     Next (nextinstr_nf (rs#EAX <- (Val.divu rs#EAX (rs#EDX <- Vundef)#r1) *)
  (*                           #EDX <- (Val.modu rs#EAX (rs#EDX <- Vundef)#r1))) m *)
  (* | Pidiv r1 => *)
  (*     Next (nextinstr_nf (rs#EAX <- (Val.divs rs#EAX (rs#EDX <- Vundef)#r1) *)
  (*                           #EDX <- (Val.mods rs#EAX (rs#EDX <- Vundef)#r1))) m *)
  (* | Pand_rr rd r1 => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m *)
  (* | Pand_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m *)
  (* | Por_rr rd r1 => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m *)
  (* | Por_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m *)
  (* | Pxor_rr rd r1 => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m *)
  (* | Pxor_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m *)
  (* | Psal_rcl rd => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#ECX))) m *)
  (* | Psal_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m *)
  (* | Pshr_rcl rd => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#ECX))) m *)
  (* | Pshr_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m *)
  (* | Psar_rcl rd => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#ECX))) m *)
  (* | Psar_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m *)
  (* | Pror_ri rd n => *)
  (*     Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m *)
  (* | Pcmp_rr r1 r2 => *)
  (*     Next (nextinstr (compare_ints (rs r1) (rs r2) rs)) m *)
  (* | Pcmp_ri r1 n => *)
  (*     Next (nextinstr (compare_ints (rs r1) (Vint n) rs)) m *)
  (* | Ptest_rr r1 r2 => *)
  (*     Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs)) m *)
  (* | Ptest_ri r1 n => *)
  (*     Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs)) m *)
  (* | Pcmov c rd r1 => *)
  (*     match eval_testcond c rs with *)
  (*     | Some true => Next (nextinstr (rs#rd <- (rs#r1))) m *)
  (*     | Some false => Next (nextinstr rs) m *)
  (*     | None => Stuck *)
  (*     end *)
  (* | Psetcc c rd => *)
  (*     match eval_testcond c rs with *)
  (*     | Some true => Next (nextinstr (rs#ECX <- Vundef #EDX <- Vundef #rd <- Vtrue)) m *)
  (*     | Some false => Next (nextinstr (rs#ECX <- Vundef #EDX <- Vundef #rd <- Vfalse)) m *)
  (*     | None => Stuck *)
  (*     end *)
  (* (** Arithmetic operations over floats *) *)
  (* | Paddd_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m *)
  (* | Psubd_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m *)
  (* | Pmuld_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m *)
  (* | Pdivd_ff rd r1 => *)
  (*     Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m *)
  (* | Pnegd rd => *)
  (*     Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m *)
  (* | Pabsd rd => *)
  (*     Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m *)
  (* | Pcomisd_ff r1 r2 => *)
  (*     Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m *)
  (* (** Branches and calls *) *)
  (* | Pjmp_l lbl => *)
  (*     goto_label c lbl rs m *)
  (* | Pjmp_s id => *)
  (*     Next (rs#PC <- (symbol_offset id Int.zero)) m *)
  (* | Pjmp_r r => *)
  (*     Next (rs#PC <- (rs r)) m *)
  (* | Pjcc cond lbl => *)
  (*     match eval_testcond cond rs with *)
  (*     | Some true => goto_label c lbl rs m *)
  (*     | Some false => Next (nextinstr rs) m *)
  (*     | None => Stuck *)
  (*     end *)
  (* | Pjmptbl r tbl => *)
  (*     match rs#r with *)
  (*     | Vint n =>  *)
  (*         match list_nth_z tbl (Int.signed n) with *)
  (*         | None => Stuck *)
  (*         | Some lbl => goto_label c lbl (rs #ECX <- Vundef #EDX <- Vundef) m *)
  (*         end *)
  (*     | _ => Stuck *)
  (*     end *)
  (* | Pcall_s id => *)
  (*     Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (symbol_offset id Int.zero)) m *)
  (* | Pcall_r r => *)
  (*     Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (rs r)) m *)
  (* | Pret => *)
  (*     Next (rs#PC <- (rs#RA)) m *)
  (* (** Pseudo-instructions *) *)
  (* | Plabel lbl => *)
  (*     Next (nextinstr rs) m *)
  (* | Pallocframe lo hi ofs_ra ofs_link => *)
  (*     let (m1, stk) := Mem.alloc m lo hi in *)
  (*     let sp := Vptr stk (Int.repr lo) in *)
  (*     match Mem.storev Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with *)
  (*     | None => Stuck *)
  (*     | Some m2 => *)
  (*         match Mem.storev Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with *)
  (*         | None => Stuck *)
  (*         | Some m3 => Next (nextinstr (rs#ESP <- sp)) m3 *)
  (*         end *)
  (*     end *)
  (* | Pfreeframe lo hi ofs_ra ofs_link => *)
  (*     match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with *)
  (*     | None => Stuck *)
  (*     | Some ra => *)
  (*         match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with *)
  (*         | None => Stuck *)
  (*         | Some sp => *)
  (*             match rs#ESP with *)
  (*             | Vptr stk ofs => *)
  (*                 match Mem.free m stk lo hi with *)
  (*                 | None => Stuck *)
  (*                 | Some m' => Next (nextinstr (rs#ESP <- sp #RA <- ra)) m' *)
  (*                 end *)
  (*             | _ => Stuck *)
  (*             end *)
  (*         end *)
  (*     end *)
  (* | Pbuiltin ef args res => *)
  (*     Stuck                             (**r treated specially below *) *)

  | _ => None
  end.


Fixpoint symExec (c : code) (v : ValMap) : ValMap :=
  match c with
    | nil => v
    | i :: is => symExec is (single_symExec i v)
  end. *) 

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