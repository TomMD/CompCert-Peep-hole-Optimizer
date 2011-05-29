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
Require Import Peephole.
Require Import Asm.
Require Import PeepholeLocations.


(* symbolic flags matching proposition. A flag is considered to match
   if it has the same value between two states, or if in the left state
   it is undefined. We consider it valid for a flag to become more
   defined. *)
Inductive symFlags_match : crbit -> SymState -> SymState -> Prop :=
| symFlags_match_exact : 
  forall (f : crbit)  (s1 s2 : SymState),
    lookup (Register (CR f)) (symLocs s1) = lookup (Register (CR f)) (symLocs s2) ->
    symFlags_match f s1 s2
| symFlags_match_def : 
  forall f s1 s2,
    lookup (Register (CR f)) (symLocs s1) = symUndef ->
    symFlags_match f s1 s2.

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


(* so, here is a trivial match Prop for symbolic states. it needs to be fleshed out *)
Inductive symStates_match : SymState -> SymState -> Prop :=
| symStates_match_intro : forall s1 s2, symStates_match s1 s2.
  
  

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

Lemma peephole_validate_correct : forall (c d : code),
  peephole_validate c d = true -> forall (s : SymState),
    symExec c s = symExec d s.
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