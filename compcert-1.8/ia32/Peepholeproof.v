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

Require Import Coq.Lists.List.

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

(** Utility lemmas and tactics -- 

    the following lemmas and tactics are
    just helpful bits to clean up the automation of further proofs in this
    file.
*)

(* extract the left argument from a boolean conjunction hypothesis *)
Lemma andb_true_left : forall a b,
  a && b = true -> a = true.
Proof.
  intros; symmetry in H; apply andb_true_eq in H;
  inversion H; auto.
Qed.

(* extract the right argument from a boolean conjunction hypothesis *)
Lemma andb_true_right : forall a b,
  a && b = true -> b = true.
Proof.
  intros; symmetry in H; apply andb_true_eq in H;
  inversion H; auto.
Qed. 


(* tactics for manipulating boolean conjunction hypotheses and
extracting all the operands into separate hypotheses. *)

Ltac split_andb' H := 
  let H0 := fresh "H" in assert (H0 := H); 
    apply andb_true_left in H; apply
      andb_true_right in H0.

Ltac split_andb :=
  repeat
    match goal with
      | [ H : _ && _ = true |- _ ] => split_andb' H
    end. 

(* we do lots of inversion of beq_SymExpr based hypotheses. For
clarity, this tactic makes it explicit when we do this. *)
Ltac invert_beq_SymExpr :=
  match goal with
    | [ H : beq_SymExpr _ _ = true |- _ ] => inversion H
  end.

(* lemmas about single steps in our symbolic execution *)
Lemma symExec_first_instr : forall a c initS S,
  symExec (a::c) initS = Some S ->
  exists S', single_symExec a initS = Some S'.
Proof.
  intros; simpl in *.
  match goal with
    | [ H : match ?O with | Some _ => _ | None => _ end = _ |- _ ] =>
      destruct O; [eexists; reflexivity | inversion H ]
  end.
Qed.

Lemma symExec_step: forall a c initS S S', 
      symExec (a::c) initS = Some S -> 
      single_symExec a initS = Some S' ->
      symExec c S' = Some S.
Proof.
  intros.
  unfold symExec in H.
  rewrite H0 in H. rewrite <- H. reflexivity.
Qed.



(** Decision Procedure Correctness Proofs --
    
    For all of our
    boolean decision procedures, we would like to show that they are
    correct -- if beq_* a b = true then a = b. These lemmas are useful
    in the overall correctness proofs of peephole_validate 
*)

Lemma beq_SymOp_correct : forall a b, beq_SymOp a b = true -> a = b.
Proof.
  induction a ; intros ; destruct b ; try reflexivity ; try inversion H.
Qed.

Lemma beq_val_correct : forall a b, beq_val a b = true -> a = b.
Proof.
  Ltac case_val_eq :=
    match goal with
      | [ H : (if val_eq ?L ?R then _ else _) = true |- _ ] =>
      case_eq (val_eq L R); intros case CASE; auto; rewrite CASE in H; inversion H
    end.

  induction a ; intros; try (
    unfold beq_val in H; 
      match goal with 
        | [ _ : _ |- _ = ?B ] => destruct B; inversion H
      end);
  try reflexivity; try case_val_eq.
Qed.

Lemma beq_Loc_correct : forall a b, beq_Loc a b = true -> a = b.
Proof.
  induction a ; intros.
  destruct b.
  unfold beq_Loc in H. case_eq (Loc_eq (Register p) (Register p0)).
  intros. assumption. intros.
  rewrite H0 in H. inversion H. discriminate.
  
  destruct b ; inversion H.
  unfold beq_Loc in H.
  case_eq (Loc_eq (Memory a) (Memory a0)) ; intros.
  auto.  rewrite H0 in H. inversion H.
Qed.

Lemma beq_addrmode_correct : forall a b, beq_addrmode a b = true -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction a ; intros.
  destruct b.
  unfold beq_addrmode in H.
  match goal with
    | [ H : (if addrmode_eq ?l ?r then _ else _) = _ |- _] => case_eq (addrmode_eq l r) ; intros
  end.
  auto.
  rewrite H0 in H. inversion H.
Qed.



Lemma beq_SymExpr_correct : forall a b, beq_SymExpr a b = true -> a = b.
Proof.
  intro a.
  induction a using SymExpr_ind'; intros;
    destruct b; try (invert_beq_SymExpr; try (apply IHa in H1; subst; auto)).

  (* case: binOp *)
  split_andb;
  apply IHa1 in H2;
  apply IHa2 in H0;
  apply beq_SymOp_correct in H1; subst; auto.

  (* case: Imm *)
  apply beq_val_correct in H; subst; auto.

  (* case: Initial *)
  apply beq_Loc_correct in H; subst; auto. 

  (* case: Load *)
  split_andb.

(* Here it gets ugly... but its done... come clean this up. *)
  assert (le = l0). 

  clear H0 H2 H1.
  generalize dependent l0.
  induction le; intros. destruct l0. reflexivity. inversion H3.
  destruct l0. inversion H3.
  assert (a1 = s). apply H. split_andb; assumption.
  rewrite H0; f_equal. apply IHle. apply H. split_andb. assumption.

  apply beq_addrmode_correct in H1.
  f_equal; auto.
  case_eq (list_eq_dec addrmode_eq la l). intros. assumption.
  intros n contra; rewrite contra in H2. inversion H2.
Qed.


Lemma beq_SymExpr_same : forall a, beq_SymExpr a a = true.
Proof.
  induction a using SymExpr_ind'; intros. simpl.
  rewrite IHa1. rewrite IHa2. unfold beq_SymOp.
  case_eq (SymOp_eq o o). intros. reflexivity. intros. elimtype False.
  auto.
Admitted.


(** Symbolic States Match --

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


(**  Lemmas and Theorems about Symbolic State Matches --
   
   The goal here is to build up to a general correctness proof of the
   peephole_validate function. That proof should state that if
   peepholve_validate accepts a piece of optimized code, then it
   follow that the symbolic states after execution of the regular and
   optimized code should match according to the symState_match
   predicate.

*) 


(* First we have some lemmas showing the correctness of the various
   helper functions that support peephole_validate. We show here that
   each of these functions is correct relative to the specification of
   symStates_match. These correctness proofs will be composed to
   develop the overall correctness proof of peephole_validate. *)

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
  unfold validFlag in H; apply orb_prop in H; inversion H; apply beq_SymExpr_correct in H0; auto.
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

(* not sure we need this... but it occured to me. Admitted, but
appears trivial with the right automation *)
Lemma symAllFlags_match__validFlags : forall s1 s2,
  symAllFlags_match s1 s2 ->
  validFlags s1 s2 = true.
Proof.
  intros. inversion H; subst;
  repeat
    match goal with
      | [ H: symFlags_match _ _ _ |- _ ] => inversion H; clear H; subst
    end.
  unfold validFlags. unfold validFlag. rewrite H1. rewrite H2. rewrite H3. rewrite H4. simpl.
  repeat rewrite beq_SymExpr_same. repeat rewrite orb_true_r. reflexivity.
Admitted.


(** Here we have lemmas and proofs about peephole_validate itself. *)
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

Lemma peephole_validate__validFlags : forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  validFlags s1 s2 = true.
Proof.  
  induction c; destruct d. intros. inversion H. intros; inversion H.
  intros;
  
  unfold peephole_validate in H;  rewrite H0 in H;  rewrite H1 in H; simpl in H;
    split_andb; assumption.

  intros. let h := fresh "H" in (assert (h := H); apply peephole_validate_length in h; inversion h as [L1 L2]; clear h L1).

  unfold peephole_validate in H;  rewrite H0 in H;  rewrite H1 in H; simpl in H;
  simpl in L2; rewrite L2 in H; split_andb; assumption.
Qed.

Theorem peephole_validate__symFlags_match : forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  symAllFlags_match s1 s2.
Proof.
  intros. assert (validFlags s1 s2 = true).
  eapply peephole_validate__validFlags.
  eassumption. assumption. assumption.
  apply validFlags_symAllFlags_match. assumption.
Qed. 


(** The overall correctness proof for peephole_validate. *)
Theorem peephole_validate_correct : forall (c d : code) (s1 s2 : SymState),
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
