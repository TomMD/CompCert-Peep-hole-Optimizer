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

Lemma beq_preg_correct : forall a b, beq_preg a b = true -> a = b.
Proof.
  Ltac case_preg_eq :=
    match goal with
      | [ H : (if preg_eq ?L ?R then _ else _) = true |- _ ] =>
        case_eq (preg_eq L R); intros case CASE; auto; rewrite CASE in H; inversion H
    end.

  induction a ; intros ; try (
    unfold beq_preg in H;
  match goal with
    | [ _ : _ |- _ = ?B ] => destruct b; inversion H
  end);
  try reflexivity ; try case_preg_eq.
Qed.

Lemma beq_SymExpr_Load_a : forall a b la le lb lf,
  beq_SymExpr (Load a la le) (Load b lb lf) = true -> beq_SymExpr a b = true.
Proof.
  induction a using SymExpr_ind' ; intros ;
    try (destruct b; try (simpl in H; split_andb; inversion H0);
      simpl in H ; split_andb; reflexivity).

  destruct b ; try (simpl in H; split_andb; inversion H0; fail).
  simpl in H. split_andb. simpl. rewrite H0, H1, H2. reflexivity.

  destruct b; try (simpl in H1; split_andb; inversion H2; fail).
  simpl in H1. split_andb. simpl. rewrite H2, H3, H4. reflexivity.
Qed.

Lemma beq_SymExpr_la_inductive : forall a b la le lb lf x y,
  beq_SymExpr (Load a (x::la) le) (Load b (y::lb) lf) = true ->
  beq_SymExpr (Load a la le) (Load b lb lf) = true.
Proof.
  destruct la ; intros. destruct lb. simpl in H. split_andb.
  simpl. rewrite H0, H1. reflexivity.

  simpl in H. split_andb. inversion H2.
  simpl in H. split_andb. simpl. rewrite H0,H1,H2. 
  reflexivity. 
Qed.

Lemma beq_SymExpr_le_inductive: forall a b la le lb lf x y,
  beq_SymExpr (Load a la (x::le)) (Load b lb (y::lf)) = true ->
  beq_SymExpr (Load a la le) (Load b lb lf) = true.
Proof.
  destruct le ; intros. destruct lf. simpl in H. split_andb.
  simpl. rewrite H, H0.  reflexivity.
  simpl in H. split_andb. inversion H2.
  simpl in H. split_andb. inversion H2.
  simpl in H. split_andb. simpl. rewrite H, H0, H2.  reflexivity.
Qed.

Lemma beq_SymExpr_correct : forall a b, beq_SymExpr a b = true -> a = b.
Proof.
  intro a.
  induction a using SymExpr_ind'; intros;
    destruct b; 
      try (invert_beq_SymExpr; split_andb; 
        try (apply IHa in H1; subst; auto)).

  (* case: binOp *)
  apply IHa1 in H2;
  apply IHa2 in H0;
  apply beq_SymOp_correct in H1; subst; reflexivity. 

  (* case: Imm *)
  apply beq_val_correct in H; subst; auto.

  (* case: InitialReg *)
  apply beq_preg_correct in H ; subst; auto.

  (* case: Load *)
  f_equal.
  apply IHa. assumption.
  
  generalize dependent l.
  induction la; intros. case_eq l. reflexivity. intros. subst. inversion H3.
  case_eq l; intros; subst. inversion H3.
  f_equal. apply H. split_andb. assumption.
  apply IHla. apply H. apply (beq_SymExpr_la_inductive _ _ _ _ _ _ a0 s). apply H1.
  split_andb. assumption.

  generalize dependent l0.
  induction le ; intros. case_eq l0. reflexivity. intros. subst. inversion H4.
  case_eq l0; intros; subst. inversion H4.
  f_equal. apply H0. split_andb. assumption.
  apply IHle. apply H0. eapply beq_SymExpr_le_inductive. apply H1.
  split_andb. assumption.
Qed.

(* This lemma is probably too strong... we might want some kind of
inductive relation on memory states instead *)
Lemma beq_MemState_correct : forall a b, 
  beq_MemState a b = true -> a = b.
Proof.
  induction a. destruct b. reflexivity. intro H. simpl in H. inversion H.

  destruct b. simpl. intro H; destruct a in H; inversion H.
  intro.
  simpl in H. destruct a. destruct p. 

  split_andb. apply beq_SymExpr_correct in H.
  apply beq_SymExpr_correct in H1.
  subst. f_equal. apply IHa; auto.
Qed.

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
    (forall l, false = isCR l ->
      normalize (lookup l (symReg s1)) = normalize (lookup l (symReg s2))) ->
    symAllRegs_match s1 s2.

Inductive symMemory_match : SymState -> SymState -> Prop :=
| symMemory_match_intro : 
  forall s1 s2,
    normalizeMem (store (symMem s1)) = normalizeMem (store (symMem s2)) -> 
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

Lemma validRegs__symAllRegs_match_pre : forall s1 s2,
  validRegs s1 s2 = true -> 
   (forall l, false = isCR l ->
    normalize (lookup l (symReg s1)) = normalize (lookup l (symReg s2))).
Proof.
  intros s1 s2;
    destruct s1; destruct s2; 
      intro H; simpl in H; split_andb;
      intros REG notCR; 
          apply beq_SymExpr_correct; simpl;
            induction REG; intros; try assumption; 
        (* integer registers *)
        try (induction i; assumption); 
        (* float registers *)
          try (induction f; assumption);
        (* flags... *)
        inversion notCR.
Qed.

Lemma peephole_validate__validRegs:  forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  validRegs s1 s2 = true.
Proof.
  induction c; destruct d; intros; try (inversion H; fail); [
  unfold peephole_validate in H; rewrite H0 in H; rewrite H1 in H; simpl in H;
  split_andb; assumption |

  let h := fresh "H" in 
    (assert (h := H); 
      apply peephole_validate_length in h; 
        inversion h as [L1 L2]; 
          clear h L1);

  unfold peephole_validate in H; 
    rewrite H0 in H; rewrite H1 in H; 
      simpl in H; simpl in L2; rewrite L2 in H; split_andb; assumption ].
Qed.
  
Theorem peephole_validate__symRegs_match : forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  symAllRegs_match s1 s2.
Proof.
  intros;

  assert (PRE : forall l, false = isCR l ->
    normalize (lookup l (symReg s1)) = normalize (lookup l (symReg s2))) by
  (apply (peephole_validate__validRegs c d s1 s2) in H;
    try (apply validRegs__symAllRegs_match_pre; assumption; fail); try assumption);
   eapply (symAllRegs_match_intro s1 s2); apply PRE.
Qed.


Theorem peephole_validate__symMemory_match : forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  symMemory_match s1 s2.
Proof.
  destruct c; destruct d; intros;
  try (unfold peephole_validate in H; simpl in H; inversion H; fail).
  unfold peephole_validate in H; rewrite H0 in H; rewrite H1 in H;
    simpl in H; split_andb. unfold validMem in H3. apply beq_MemState_correct in H3.
    constructor. assumption.

  let h := fresh "H" in 
    (assert (h := H); 
      apply peephole_validate_length in h; 
        inversion h as [L1 L2]; 
          clear h L1); simpl in L2;
  unfold peephole_validate in H; rewrite H0 in H; rewrite H1 in H;
    simpl in H; rewrite L2 in H;  split_andb. 
  unfold validMem in H3; apply beq_MemState_correct in H3; constructor; assumption.
Qed.

Theorem peephole_validate__subset_constraints : forall c d s1 s2,
  peephole_validate c d = true ->
  symExec c initSymSt = Some s1 -> 
  symExec d initSymSt = Some s2 ->
  subset (constraints s1)(constraints s2) = true.
Proof.
  destruct c; destruct d; intros;
  try (unfold peephole_validate in H; simpl in H; inversion H; fail).

  unfold peephole_validate in H; rewrite H0 in H; rewrite H1 in H;
  simpl in H; split_andb; unfold validConstraints in *; assumption.
    
  let h := fresh "H" in 
    (assert (h := H); 
      apply peephole_validate_length in h; 
        inversion h as [L1 L2]; 
          clear h L1); simpl in L2;
  unfold peephole_validate in H; rewrite H0 in H; rewrite H1 in H;
  simpl in H; rewrite L2 in H; split_andb; unfold validConstraints in *; assumption.

Qed.
  

(** The overall correctness proof for peephole_validate within the our 
   definition of symbolic equivalence. *)
Theorem peephole_validate_correct : forall (c d : code) (s1 s2 : SymState),
  peephole_validate c d = true -> 
    symExec c initSymSt = Some s1 -> 
    symExec d initSymSt = Some s2 ->
    symStates_match s1 s2.
Proof.
  intros.
  constructor.
  apply (peephole_validate__symFlags_match c d); auto.
  apply (peephole_validate__symRegs_match c d); auto.
  apply (peephole_validate__symMemory_match c d); auto.
  apply (peephole_validate__subset_constraints c d); auto.
Qed.

Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: peephole_transf_program prog = Errors.OK tprog.

(* If we had a way to connect our symbolic world to the CompCert semantic 
   world, this is where it would end up... *)
Lemma transf_final_states:
  forall match_states st1 st2 r, 
  match_states st1 st2 -> Asm.final_state st1 r -> Asm.final_state st2 r.
Proof.
Admitted.

Theorem transf_program_correct :
  forall (beh: program_behavior), not_wrong beh ->
  Asm.exec_program prog beh -> Asm.exec_program tprog beh.
Proof.
Admitted.

End PRESERVATION.
(* lemma 1

Let b be a block and c an instruction list starting with
a branching instruction. If Σ |- (b; c), R, F, M →* c, R', F', M'
and α(b) = (m, s), then Σ|- [[m]](R, F, M ) = (R', F', M') and
Σ, (R, F, M ) |= s. *) 
(*
Inductive constraintSatisfied : Constraint -> regset -> mem -> Prop :=
  | readConst  : forall c rs m,
    c = ReadMem (cnk,a) -> memLoad cnk m a rs (IReg EAX) <> None -> constraintSatisfied c rs m
  | writeConst : forall c rs m,
    c = WriteMem (cnk,a) -> memStore cnk m a rs (IReg EAX) <> None -> constraintSatisfied c rs m
  | divConst   : forall c rs m,
    c = DivBy e -> .

Inductive constraintsSatisfied : list Constraint -> regset -> mem -> Prop :=
  | noConstraints : forall c rs m, nil = c -> constraintsSatisfied c rs m
  | allSubConstraintsMatch : forall c rs m, 
    forall x xs, x::xs = c -> constraintSatisfied x rs m -> constraintsSatisfied xs rs m ->
      constraintsSatisfied c rs m.


Lemma semantics_symExec_same_state : forall (c : code) (rs : regset) (m : mem) (st : SymState),
  symExec c initSymSt  = Some (SymSt s' m' r') ->
  exec_instrs c rs m  = Next r'' m'' ->
  symMemEqSemMem m' m'' /\ symRegEqSemReg r' r''
  /\
  constraintsSatisfied s' rs m.
*)
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
