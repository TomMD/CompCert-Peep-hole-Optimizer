Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.
Require Import Asm.
Require Import Peephole.
Require Import PeepholeLocations.

(* lemma 1

Let b be a block and c an instruction list starting with
a branching instruction. If Σ |- (b; c), R, F, M →* c, R', F', M'
and α(b) = (m, s), then Σ|- [[m]](R, F, M ) = (R', F', M') and
Σ, (R, F, M ) |= s. *) 

(* lemma 2

Let b be a block and c an instruction list starting with a branching
instruction. Let α(b) = (m, s). If Σ, (R,F,M) |= s, then there exists
R', F', M' such that Σ|- (b; c), R, F, M →* c, R , F , M

*)   


(* lemma 3

let b1, b2 be two blocks and c1,c2, two instruction sequences starting
with branching instructions. If V(b1,b2) = true and Σ|-(b1;c1),R,F,M
->* c1,R',F',M' then Σ |- (b2;c2), R, F, M ->* c2,R',F',M'

*)


(** Symbolic States Match

   Here we define a series of Inductive Propositions which define what
   it means for two symbolic states to be equivalent. This is
   different than strict equality, particularly in the case of
   flags. We allow flags becoming more defined to still equate to
   equivalence. *)

Inductive symFlags_match : crbit -> SymState -> SymState -> Prop :=
| symFlags_match_exact : 
  forall (f : crbit)  (s1 s2 : SymState),
    lookup (CR f) (symReg s1) = lookup (CR f) (symReg s2) ->
    symFlags_match f s1 s2
| symFlags_match_def : 
  forall f s1 s2,
    lookup (CR f) (symReg s1) = symUndef ->
    symFlags_match f s1 s2.

Lemma symFlags_match_cases :
  forall cr s1 s2,
  symFlags_match cr s1 s2 -> 
  lookup (CR cr) (symReg s1) = lookup  (CR cr) (symReg s2) \/
  lookup (CR cr) (symReg s1) = symUndef.
Proof.
  intros; inversion H; [left; assumption | right; assumption].
Qed.

Lemma symFlags_cases_match :
  forall cr s1 s2,
  lookup (CR cr)  (symReg s1) = lookup (CR cr) (symReg s2) \/
  lookup (CR cr) (symReg s1) = symUndef ->
  symFlags_match cr s1 s2.
Proof. 
  intros; inversion H; [
  apply symFlags_match_exact ; assumption |
  apply symFlags_match_def ; assumption].
Qed.

Inductive symAllFlags_match : SymState -> SymState -> Prop :=
| symAllFlags_match_intro:
  forall s1 s2,
    symFlags_match ZF s1 s2 ->
    symFlags_match CF s1 s2 ->
    symFlags_match PF s1 s2 ->
    symFlags_match SOF s1 s2 ->
    symAllFlags_match s1 s2.

Inductive symAllRegs_match : SymState -> SymState -> Prop :=
| symAllRegs_match_intro :
  forall s1 s2,
    forall l, (false = isCR l ->
              lookup l (symReg s1) = lookup l (symReg s2)) ->
    symAllRegs_match s1 s2.

Inductive symMemory_match : SymState -> SymState -> Prop :=
| symMemory_match_intro : 
  forall s1 s2,
    symMemory_match s1 s2.

Inductive symStates_match : SymState -> SymState -> Prop :=
| symStates_match_intro : 
  forall s1 s2, 
    symAllFlags_match s1 s2 ->
    symAllRegs_match s1 s2 ->
    symMemory_match s1 s2 ->
    subset (constraints s1) (constraints s2) = true ->
    symStates_match s1 s2.

Require Import Coq.Lists.List.


Lemma andb_true_left : forall a b,
  a && b = true -> a = true.
Proof.
  intros; symmetry in H; apply andb_true_eq in H;
  inversion H; auto.
Qed.

(* Some lemmas related to the above propositions *)

(* REPLACE ME WITH THE REAL LEMMA!!! *)
Lemma beq_SymExpr_true : forall a b,
  beq_SymExpr a b = true -> a = b.
Proof.
Admitted.

Lemma validFlags__validFlag : forall f s1 s2,
  validFlags s1 s2 = true -> validFlag (Register (CR f)) s1 s2 = true.
Proof.
  Ltac intFlags := intros; match goal with
                             | [ H: validFlags _ _ = true |- _] => unfold validFlags in H
                           end.
  induction f; intFlags; [
    rewrite <- andb_assoc in H; rewrite <- andb_assoc in H |
      rewrite <- andb_assoc in H; rewrite andb_comm in H; rewrite <- andb_assoc in H |
        rewrite <- andb_assoc in H; rewrite <- andb_assoc in H; rewrite andb_comm in H;
          rewrite <- andb_assoc in H |
            rewrite andb_comm in H ];
  apply andb_true_left in H; assumption.
Qed.
  
  
Lemma validFlag__eq_or_undef : forall f s1 s2,
  validFlag (Register (CR f)) s1 s2 = true -> 
  lookup (CR f) (symReg s1) = lookup (CR f) (symReg s2) \/
  lookup (CR f) (symReg s1) = symUndef.
Proof.
  intros;
  unfold validFlag in H; apply orb_prop in H; inversion H; apply beq_SymExpr_true in H0; auto.
Qed.
 
Lemma validFlags_symAllFlags_match : forall (s1 s2 : SymState),
    validFlags s1 s2 = true -> 
    symAllFlags_match s1 s2.
Proof.

  Ltac assertFlag := match goal with
                       | [ H: _ |- symFlags_match ?F ?S1 ?S2 ] => 
                         assert (validFlag (Register F) S1 S2 = true)
                           by (apply validFlags__validFlag; assumption)
                     end.
  intros s1 s2 Hcr; 
    apply symAllFlags_match_intro; assertFlag;
      apply symFlags_cases_match; apply validFlag__eq_or_undef; assumption.
Qed.

Lemma peephole_validate_length : forall (c d : code),
  peephole_validate c d = true -> 
  (length c <> 0)%nat /\ Compare_dec.leb (length d)  (length c) = true.
Proof.
  destruct c; intros.
  inversion H.
  split.
  simpl. discriminate.
  simpl in H.
  match goal with
    | [ _ : (if ?B then _ else _) = _ |- _ ] => case_eq B
  end.
  intros. auto. 
  intro contra. rewrite contra in H. inversion H.
Qed.  

Lemma peephole_validate_correct : forall (c d : code) (s1 s2 : SymState),
  peephole_validate c d = true -> 
    symExec c initSymSt = Some s1 -> 
    symExec d initSymSt = Some s2 ->
    symStates_match s1 s2.
Proof.
  destruct c.
  intros. inversion H.
  destruct d.
  intros. simpl in H. unfold sameSymbolicExecution in H.
  destruct (single_symExec i initSymSt).
  unfold peephole_validate in H.
  simpl in H.
Admitted.
(*
  rewrite H0 in H. simpl in H.
  
  match goal with
    | [ _ : (if ?B then _ else _) = _ |- _ ] => destruct B
  end.
  inversion H.

  assert (Compare_dec.leb (@length instruction nil) (length (i::c)) = true) by
    (apply peephole_validate_length in H; inversion H; auto).
  
*)
Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: peephole_transf_program prog = Errors.OK tprog.

Theorem peephole_correct :
   forall (match_states : Asm.state -> Asm.state -> Prop)
          (measure : Asm.state -> nat)
          (st1 : state) (t : trace) (st1' : state),
   step (Genv.globalenv prog) st1 t st1' ->
   forall st2 : state,
   match_states st1 st2 ->
   (exists st2' : state,
      plus step (Genv.globalenv tprog) st2 t st2' /\ match_states st1' st2') \/
   (measure st1' < measure st1)%nat /\ t = E0 /\ match_states st1' st2.
Proof. Admitted.

Lemma transf_initial_states:
  forall match_states st1, Asm.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
Admitted.
(*   intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (symbol_offset (Genv.globalenv tprog) (prog_main tprog) Int.zero)
     with (Vptr fb Int.zero).
  econstructor; eauto. constructor. apply Mem.extends_refl.
  split. auto. unfold parent_sp; congruence.
  intros. repeat rewrite Pregmap.gso; auto with ppcgen.
  destruct r; simpl; congruence.
  unfold symbol_offset. 
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. unfold ge; rewrite H1. auto. *)


Lemma transf_final_states:
  forall match_states st1 st2 r, 
  match_states st1 st2 -> Asm.final_state st1 r -> Asm.final_state st2 r.
Proof.
Admitted.
(*  intros. inv H0. inv H. constructor. auto. 
  compute in H1. 
  generalize (preg_val _ _ _ AX AG). rewrite H1. intros LD; inv LD. auto.
Qed. *)

Theorem transf_program_correct :
  forall (beh: program_behavior), not_wrong beh ->
  Asm.exec_program prog beh -> Asm.exec_program tprog beh.
Proof.
Admitted.

(*
  unfold exec_program; intros.
  (* the below is a "proof" of hte same form as Mach -> Asm, but it's
  not the right approach i think.... but it suggests a future
  path... *)
  eapply simulation_star_preservation; eauto.  
  eexact  transf_initial_states.  
  eexact transf_final_states.  
  eexact peephole_correct.  
Qed. *)

End PRESERVATION.
(* above I've sketched in the proof, based on Mach->Asm and stubbed in
major lemmas. After some thought, thought though, I think this may not
be the right approach. We aren't showing that two different kinds of
things have the same semantic, but instead that two of the same kind
of thing hav ethe same semantic. This is different in important ways. 

The statement of the final theorem, though is the correct theorem. I'm
not sure, it requires more thought. *)
