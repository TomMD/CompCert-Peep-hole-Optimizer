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

Lemma beq_SymOp_true : forall a b, beq_SymOp a b = true -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction a ; intros ; destruct b ; try reflexivity ; try inversion H.
Qed.

Lemma beq_val_true : forall a b, beq_val a b = true -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction a ; intros.
  unfold beq_val in H. destruct b ; inversion H. reflexivity.
  unfold beq_val in H. destruct b ; inversion H.
Admitted.

Lemma beq_Loc_true : forall a b, beq_Loc a b = true -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction a ; intros.
  destruct b.
  unfold beq_Loc in H. case_eq (Loc_eq (Register p) (Register p0)).
  intros. assumption. intros.
Admitted.

Lemma beq_addrmode_true : forall a b, beq_addrmode a b = true -> a = b.
Proof.
  intros.
  generalize dependent b.
  induction a ; intros.
  destruct b.
Admitted.

Definition admit {T: Type} : T.  Admitted.

Require Import Crush.

Lemma beq_SymExpr_true : forall a b, beq_SymExpr a b = true -> a = b.
Proof.
  intros.  generalize dependent b.
  induction a.  intros.

  simpl in H. destruct b ; crush.

  (* case: binOp true *)
  case_eq (beq_SymOp s s0). intros. apply beq_SymOp_true in H0.
  rewrite H0.  assert (a1 = b1).
    case_eq (beq_SymExpr a1 b1).
    intros. apply IHa1. assumption.
    intros. rewrite H1 in H.
    rewrite andb_comm with (b2 := false) in H. inversion H.

    rewrite H1.
    case_eq (beq_SymExpr a2 b2).
    intros. assert (a2 = b2). apply IHa2.
    assumption. rewrite H3. reflexivity.
    intros. rewrite H2 in H.
    rewrite andb_comm with (b2 := false) in H. inversion H.

  (* case: binOp false *)
    intros. rewrite H0 in H. inversion H.
  
  (* case: neg *)
    intros. destruct b ; crush.
    assert (a = b). apply IHa. assumption.
    rewrite H0. reflexivity.

  (* case: abs_f *)
    intros. destruct b ; crush.
    assert (a = b). apply IHa. assumption.
    rewrite H0. reflexivity.

    intros. destruct b ; crush.
    assert (a = b). apply IHa. assumption.
    rewrite H0. reflexivity.

    intros. destruct b ; crush.
    apply beq_val_true in H.  rewrite H. reflexivity.

    intros. destruct b ; crush.
    assert (l = l0). apply beq_Loc_true in H. rewrite H. reflexivity.
    rewrite H0. reflexivity.

    intros. destruct b. inversion H. inversion H. inversion H. inversion H. inversion H.
    inversion H.

    inversion H.  f_equal. apply sym_eq in H1. apply andb_true_eq in H1. 
    inversion H1. unfold beq_addrmode in H2.  assert (beq_addrmode a a0 = true).
    case_eq (beq_addrmode a a0). reflexivity.  intros.   rewrite H3 in H1.
    inversion H1. inversion H5.
    apply beq_addrmode_true. assumption.


    case_eq ((fix leq (x1 x2 : list (addrmode * SymExpr)) : bool :=
          match x1 with
          | nil => match x2 with
                   | nil => true
                   | _ :: _ => false
                   end
          | pair a1 v1 :: _ =>
              match x2 with
              | nil => false
              | pair a2 v2 :: _ => beq_addrmode a1 a2 && beq_SymExpr v1 v2
              end
          end) l l0). intro.

    admit.
(*
    generalize dependent l0.
    induction l ; intros. destruct l0. reflexivity.
    inversion H0.  destruct l0.
*)

    intros. rewrite H0 in H1. inversion H1.
Qed.


(** Symbolic States Match

   Here we define a series of Inductive Propositions which define what
   it means for two symbolic states to be equivalent. This is
   different than strict equality, particularly in the case of
   flags. We allow flags becoming more defined to still equate to
   equivalence. *)

Inductive symFlags_match : crbit -> SymState -> SymState -> Prop :=
| symFlags_match_exact : 
  forall (f : crbit)  (s1 s2 : SymState),
    lookup (Register (CR f)) (symLocs s1) = lookup (Register (CR f)) (symLocs s2) ->
    symFlags_match f s1 s2
| symFlags_match_def : 
  forall f s1 s2,
    lookup (Register (CR f)) (symLocs s1) = symUndef ->
    symFlags_match f s1 s2.

Lemma symFlags_match_cases :
  forall cr s1 s2,
  symFlags_match cr s1 s2 -> 
  lookup (Register (CR cr)) (symLocs s1) = lookup (Register (CR cr)) (symLocs s2) \/
  lookup (Register (CR cr)) (symLocs s1) = symUndef.
Proof.
  intros. inversion H. left. assumption. right. assumption.
Qed.

Lemma symFlags_cases_match :
  forall cr s1 s2,
  lookup (Register (CR cr)) (symLocs s1) = lookup (Register (CR cr)) (symLocs s2) \/
  lookup (Register (CR cr)) (symLocs s1) = symUndef ->
  symFlags_match cr s1 s2.
Proof. 
  intros.  inversion H.
  apply symFlags_match_exact ; assumption.
  apply symFlags_match_def ; assumption.
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
              (s1 # l) = (s2 # l)) ->
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

(* Some lemmas related to the above propositions *)
Lemma validFlags_symAllFlags_match : forall (s1 s2 : SymState),
    validFlags s1 s2 = true -> 
    symAllFlags_match s1 s2.
Proof.
  intros s1 s2 Hcr. apply symAllFlags_match_intro.
  (* Whatever works for this case will work for the others, use ';' once the proof is found *)

  apply symFlags_cases_match.
  unfold validFlags in Hcr.  unfold validFlag in Hcr. 
  apply andb_prop in Hcr. 
Admitted.

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
