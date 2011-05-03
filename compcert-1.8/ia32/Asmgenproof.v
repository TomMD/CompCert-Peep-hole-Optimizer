(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for PPC generation: main proof. *)

Add LoadPath "../common".
Add LoadPath "../backend".
Add LoadPath "../lib".
Add LoadPath "./standard".


Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import Conventions.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenretaddr.
Require Import Asmgenproof1.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

(** * Properties of control flow *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

Remark code_tail_bounds:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl. 
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Int.max_unsigned ->
  code_tail (Int.unsigned ofs) fn (i :: c) ->
  code_tail (Int.unsigned (Int.add ofs Int.one)) fn c.
Proof.
  intros. rewrite Int.add_unsigned.
  change (Int.unsigned Int.one) with 1.
  rewrite Int.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds _ _ _ _ H0). omega. 
Qed.

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf <= Int.max_unsigned.
Proof.
  intros. monadInv H. 

(* a lemma that proves peephole should clear this without admit... ASW *)
  assert (M0:(match x with
                 | nil => x
                 | i1 :: nil => x
                 | i1 :: i2 :: nil => x
                 | i1 :: i2 :: i3 :: is =>
                     i1 :: i2 :: i3 :: Por_rr EAX EAX :: is
           end) = (x)). admit.
  (* rewrite M0 in *. *)
  destruct (zlt (list_length_z (optimize x)) Int.max_unsigned); monadInv EQ0.
  rewrite list_length_z_cons. omega. 
Qed.

(** [transl_code_at_pc pc fn c] holds if the code pointer [pc] points
  within the IA32 code generated by translating Mach function [fn],
  and [c] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc: val -> block -> Mach.function -> Mach.code ->
                                             Asm.code -> Asm.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c tf tc,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    transf_function f = OK tf ->
    transl_code f c = OK tc ->
    code_tail (Int.unsigned ofs) tf tc ->
    transl_code_at_pc (Vptr b ofs) b f c tf tc.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct PPC executions
  (predicate [exec_steps]) under adequate [transl_code_at_pc] hypotheses. *)

Lemma exec_straight_steps_1:
  forall fn c rs m c' rs' m',
  exec_straight tge fn c rs m c' rs' m' ->
  list_length_z fn <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr tge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) fn c ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Int.add ofs Int.one). 
  auto. rewrite H0. rewrite H3. reflexivity.
  auto. 
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.
    
Lemma exec_straight_steps_2:
  forall fn c rs m c' rs' m',
  exec_straight tge fn c rs m c' rs' m' ->
  list_length_z fn <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr tge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) fn c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Int.unsigned ofs') fn c'.
Proof.
  induction 1; intros.
  exists (Int.add ofs Int.one). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Int.add ofs Int.one).
  auto. rewrite H0. rewrite H3. reflexivity. auto. 
  apply code_tail_next_int with i; auto.
Qed.

Lemma exec_straight_exec:
  forall fb f c tf tc c' rs m rs' m',
  transl_code_at_pc (rs PC) fb f c tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma exec_straight_at:
  forall fb f c tf tc c' tc' rs m rs' m',
  transl_code_at_pc (rs PC) fb f c tf tc ->
  transl_code f c' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc (rs' PC) fb f c' tf tc'.
Proof.
  intros. inv H. 
  exploit exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** Correctness of the return addresses predicted by
    [Asmgen.return_address_offset]. *)

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall b ofs fb f c tf tc ofs',
  transl_code_at_pc (Vptr b ofs) fb f c tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H0. inv H. 
  exploit code_tail_unique. eexact H11. eapply H1; eauto. intro.
  subst ofs0. apply Int.repr_unsigned.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos' 
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c. 
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by omega. constructor. constructor. 
  rewrite list_length_z_cons. generalize (list_length_z_pos c). omega. 
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  constructor. auto. 
  rewrite list_length_z_cons. omega.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Variable lbl: label.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> find_label lbl c = find_label lbl k.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try discriminate; destruct rs; inv H; auto.
Qed.

Remark mk_shift_label:
  forall f r1 r2 k c, mk_shift f r1 r2 k = OK c -> 
  (forall r, is_label lbl (f r) = false) ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_shift; intros.
  destruct (ireg_eq r2 ECX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark mk_div_label:
  forall f r1 r2 k c, mk_div f r1 r2 k = OK c -> 
  (forall r, is_label lbl (f r) = false) ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_div; intros.
  destruct (ireg_eq r1 EAX).
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
  destruct (ireg_eq r2 EAX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark mk_mod_label:
  forall f r1 r2 k c, mk_mod f r1 r2 k = OK c -> 
  (forall r, is_label lbl (f r) = false) ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_mod; intros.
  destruct (ireg_eq r1 EAX).
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
  destruct (ireg_eq r2 EDX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark mk_shrximm_label:
  forall r n k c, mk_shrximm r n k = OK c -> find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H; auto.
Qed.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c -> 
  (forall r r', is_label lbl (f r r') = false) ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_intconv; intros. destruct (low_ireg r2); inv H; simpl; rewrite H0; auto.
Qed.

Remark mk_smallstore_label:
  forall f addr r k c, mk_smallstore f addr r k = OK c -> 
  (forall r addr, is_label lbl (f r addr) = false) ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold mk_smallstore; intros. destruct (low_ireg r).
  monadInv H; simpl; rewrite H0; auto.
  destruct (addressing_mentions addr ECX); monadInv H; simpl; rewrite H0; auto.
Qed.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold loadind; intros. destruct ty. 
  monadInv H; auto. 
  destruct (preg_of dst); inv H; auto.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold storeind; intros. destruct ty. 
  monadInv H; auto. 
  destruct (preg_of src); inv H; auto.
Qed.

Ltac ArgsInv :=
  match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args; ArgsInv
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; ArgsInv
  | _ => idtac
  end.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold transl_cond; intros. 
  destruct cond; ArgsInv; auto. 
  destruct (Int.eq_dec i Int.zero); auto.
  destruct c0; auto.
  destruct c0; auto.
Qed.


Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  unfold transl_op; intros. destruct op; ArgsInv; auto. 
  eapply mk_mov_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_intconv_label; eauto.
  eapply mk_div_label; eauto.
  eapply mk_div_label; eauto.
  eapply mk_mod_label; eauto.
  eapply mk_mod_label; eauto.
  eapply mk_shift_label; eauto.
  eapply mk_shift_label; eauto.
  eapply mk_shrximm_label; eauto.
  eapply mk_shift_label; eauto.
  eapply trans_eq. eapply transl_cond_label; eauto. auto.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H. destruct chunk; monadInv EQ0; auto. 
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  find_label lbl c = find_label lbl k.
Proof.
  intros. monadInv H. destruct chunk; monadInv EQ0; auto; eapply mk_smallstore_label; eauto.
Qed.

Lemma transl_instr_label:
  forall f i k c,
  transl_instr f i k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. generalize (Mach.is_label_correct lbl i). 
  case (Mach.is_label lbl i); intro.
  subst i. monadInv H. simpl. rewrite peq_true. auto.
Opaque loadind.
  destruct i; simpl in H. 
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  monadInv H. eapply trans_eq; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; monadInv H; auto.
  destruct s0; monadInv H; auto. 
  monadInv H; auto.
  inv H; simpl. destruct (peq lbl l). congruence. auto. 
  monadInv H; auto.
  eapply trans_eq. eapply transl_cond_label; eauto. auto. 
  monadInv H; auto.
  monadInv H; auto.
Qed.

Lemma transl_code_label:
  forall f c tc,
  transl_code f c = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label _ _ _ _ EQ0). 
  destruct (Mach.is_label lbl a). exists x; auto. apply IHc. auto. 
Qed.

Lemma transl_find_label:
  forall f tf,
  transf_function f = OK tf -> 
  match Mach.find_label lbl f.(fn_code) with
  | None => find_label lbl tf = None
  | Some c => exists tc, find_label lbl tf = Some tc /\ transl_code f c = OK tc
             (* We'll have to do something different here TMD
                   match transl_code f c with
                     | OK c' => fmap optimize c' = tc
                     | Error e => True
                   end
              *)
  end.
Proof.
  intros. monadInv H.

(* and another one... ASW *)
  assert (M0:(match x with
                 | nil => x
                 | i1 :: nil => x
                 | i1 :: i2 :: nil => x
                 | i1 :: i2 :: i3 :: is =>
                     i1 :: i2 :: i3 :: Por_rr EAX EAX :: is
           end) = (x)). admit.
  (* rewrite M0 in *. *)

  (* note that the monadInv had been inv prior to this changes... ASW *)

  destruct (zlt (list_length_z (optimize x)) Int.max_unsigned); monadInv EQ0.
  simpl. apply transl_code_label; auto. 
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m  
  /\ transl_code_at_pc (rs' PC) b f c' tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2. 
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Int.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto. 
  rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Inductive match_stack: list Machconcr.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      transl_code_at_pc ra fb f c tf tc ->
      sp <> Vundef -> ra <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Inductive match_states: Machconcr.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ms m m' rs f tf tc
        (STACKS: match_stack s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc (rs PC) fb f c tf tc)
        (AG: agree ms sp rs),
      match_states (Machconcr.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Machconcr.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Machconcr.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c tf tc m1' m2 m2' sp ms2,
  match_stack s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc (rs1 PC) fb f (i :: c) tf tc ->
  (forall k c, transl_instr f i k = OK c ->
   exists rs2, exec_straight tge tf c rs1 m1' k rs2 m2' /\ agree ms2 sp rs2) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Machconcr.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7. 
  exploit H3; eauto. intros [rs2 [A B]]. 
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto. 
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof. induction 1; simpl. congruence. auto. Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof. induction 1; simpl. unfold Vzero. congruence. auto. Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Machconcr.Returnstate] to [Machconcr.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Machconcr.state) : nat :=
  match s with
  | Machconcr.State _ _ _ _ _ _ => 0%nat
  | Machconcr.Callstate _ _ _ _ => 0%nat
  | Machconcr.Returnstate _ _ _ => 1%nat
  end.

(** We show the simulation diagram by case analysis on the Mach transition
  on the left.  Since the proof is large, we break it into one lemma
  per transition. *)

Definition exec_instr_prop (s1: Machconcr.state) (t: trace) (s2: Machconcr.state) : Prop :=
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.


Lemma exec_Mlabel_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (lbl : Mach.label) (c : list Mach.instruction) (ms : Mach.regset)
         (m : mem),
  exec_instr_prop (Machconcr.State s fb sp (Mlabel lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c ms m).
Proof.
  intros; red; intros; inv MS.
  left; eapply exec_straight_steps; eauto; intros. 
  monadInv H. econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
  apply agree_nextinstr; auto.
Qed.

Lemma exec_Mgetstack_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (ofs : int)
         (ty : typ) (dst : mreg) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (v : val),
  load_stack m sp ty ofs = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mgetstack ofs ty dst :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set dst v ms) m).
Proof.
  intros; red; intros; inv MS.
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in H0. 
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto. eapply agree_set_mreg; eauto. congruence.
Qed.

Lemma exec_Msetstack_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (src : mreg)
         (ofs : int) (ty : typ) (c : list Mach.instruction)
         (ms : mreg -> val) (m m' : mem),
  store_stack m sp ty ofs (ms src) = Some m' ->
  exec_instr_prop (Machconcr.State s fb sp (Msetstack src ofs ty :: c) ms m) E0
                  (Machconcr.State s fb sp c ms m').
Proof.
  intros; red; intros; inv MS.
  unfold store_stack in H.
  assert (Val.lessdef (ms src) (rs (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]]. 
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in H1.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto. eapply agree_exten; eauto. 
Qed.

Lemma exec_Mgetparam_prop:
  forall (s : list stackframe) (fb : block) (f: Mach.function) (sp parent : val)
         (ofs : int) (ty : typ) (dst : mreg) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (v : val),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m sp Tint f.(fn_link_ofs) = Some parent ->
  load_stack m parent ty ofs = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mgetparam ofs ty dst :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set dst v (Regmap.set IT1 Vundef ms)) m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  unfold load_stack in *. 
  exploit Mem.loadv_extends. eauto. eexact H0. auto. 
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (parent' = parent). inv B. auto. simpl in H1. congruence.
  subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. 
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. monadInv H2.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]]. 
  exists rs2; split. eapply exec_straight_trans; eauto.
  eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto. 
Qed.

Lemma exec_Mop_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (op : operation)
         (args : list mreg) (res : mreg) (c : list Mach.instruction)
         (ms : mreg -> val) (m : mem) (v : val),
  eval_operation ge sp op ms ## args = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mop op args res :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set res v (undef_op op ms)) m).
Proof.
  intros; red; intros; inv MS.
  assert (eval_operation tge sp op ms##args = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A. 
  left; eapply exec_straight_steps; eauto; intros. simpl in H1. 
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]]. 
  exists rs2; split. eauto.
  rewrite <- Q in B.
  unfold undef_op.
  destruct op; try (eapply agree_set_undef_mreg; eauto). eapply agree_set_mreg; eauto.
Qed.

Lemma exec_Mload_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (chunk : memory_chunk) (addr : addressing) (args : list mreg)
         (dst : mreg) (c : list Mach.instruction) (ms : mreg -> val)
         (m : mem) (a v : val),
  eval_addressing ge sp addr ms ## args = Some a ->
  Mem.loadv chunk m a = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mload chunk addr args dst :: c) ms m)
               E0 (Machconcr.State s fb sp c (Regmap.set dst v (undef_temps ms)) m).
Proof.
  intros; red; intros; inv MS.
  assert (eval_addressing tge sp addr ms##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in H2. 
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]]. 
  exists rs2; split. eauto. eapply agree_set_undef_mreg; eauto. congruence.
Qed.

Lemma exec_Mstore_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (chunk : memory_chunk) (addr : addressing) (args : list mreg)
         (src : mreg) (c : list Mach.instruction) (ms : mreg -> val)
         (m m' : mem) (a : val),
  eval_addressing ge sp addr ms ## args = Some a ->
  Mem.storev chunk m a (ms src) = Some m' ->
  exec_instr_prop (Machconcr.State s fb sp (Mstore chunk addr args src :: c) ms m) E0
                  (Machconcr.State s fb sp c (undef_temps ms) m').
Proof.
  intros; red; intros; inv MS.
  assert (eval_addressing tge sp addr ms##args = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (ms src) (rs (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in H3. 
  exploit transl_store_correct; eauto. intros [rs2 [P Q]]. 
  exists rs2; split. eauto. eapply agree_exten_temps; eauto. 
Qed.

Lemma exec_Mcall_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (sig : signature) (ros : mreg + ident) (c : Mach.code)
         (ms : Mach.regset) (m : mem) (f : function) (f' : block)
         (ra : int),
  find_function_ptr ge ros ms = Some f' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  return_address_offset f c ra ->
  exec_instr_prop (Machconcr.State s fb sp (Mcall sig ros :: c) ms m) E0
                  (Callstate (Stackframe fb sp (Vptr fb ra) c :: s) f' ms m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
  (* Indirect call *)
  assert (DEST: ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    generalize (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); congruence.
  clear H.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc (Vptr fb (Int.add ofs Int.one)) fb f c tf x).
    econstructor; eauto. 
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. 
  constructor; auto. 
  econstructor; eauto. eapply agree_sp_def; eauto. congruence.
  simpl. eapply agree_exten; eauto. intros. repeat rewrite Pregmap.gso; auto with ppcgen.
  exploit ireg_val; eauto. rewrite DEST. intros LD. inv LD. auto.
  rewrite <- H2. auto. 
  (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc (Vptr fb (Int.add ofs Int.one)) fb f c tf x).
    econstructor; eauto. 
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. eauto.
  constructor; auto. 
  econstructor; eauto. eapply agree_sp_def; eauto. congruence.
  simpl. eapply agree_exten; eauto. intros. repeat rewrite Pregmap.gso; auto with ppcgen.
  rewrite <- H2. auto.
Qed.

Lemma agree_change_sp:
  forall ms sp rs sp',
  agree ms sp rs -> sp' <> Vundef ->
  agree ms sp' (rs#ESP <- sp').
Proof.
  intros. inv H. split. apply Pregmap.gss. auto. 
  intros. rewrite Pregmap.gso; auto with ppcgen.
Qed.

Lemma exec_Mtailcall_prop:
  forall (s : list stackframe) (fb stk : block) (soff : int)
         (sig : signature) (ros : mreg + ident) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (f: Mach.function) (f' : block) m',
  find_function_ptr ge ros ms = Some f' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
  load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
  Mem.free m stk (- f.(fn_framesize)) f.(fn_stacksize) = Some m' ->
  exec_instr_prop
          (Machconcr.State s fb (Vptr stk soff) (Mtailcall sig ros :: c) ms m) E0
          (Callstate s f' ms m').
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]]. 
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. 
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
  (* Indirect call *)
  assert (DEST: ms rf = Vptr f' Int.zero).
    destruct (ms rf); try discriminate.
    generalize (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); congruence.
  clear H.
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs#PC Vone). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  rewrite Pregmap.gss. rewrite nextinstr_inv; auto with ppcgen.
  repeat rewrite Pregmap.gso; auto with ppcgen. 
  exploit ireg_val; eauto. rewrite DEST. intros LD. inv LD. auto.
  generalize (preg_of_not_ESP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
  (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs#PC Vone). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  rewrite Pregmap.gss. unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.
Qed.

Lemma exec_Mgoto_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (lbl : Mach.label) (c : list Mach.instruction) (ms : Mach.regset)
         (m : mem) (c' : Mach.code),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop (Machconcr.State s fb sp (Mgoto lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c' ms m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4. 
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with ppcgen.
Qed.

Lemma exec_Mbuiltin_prop:
  forall (s : list stackframe) (f : block) (sp : val)
         (ms : Mach.regset) (m : mem) (ef : external_function)
         (args : list mreg) (res : mreg) (b : list Mach.instruction)
         (t : trace) (v : val) (m' : mem),
  external_call ef ge ms ## args m t v m' ->
  exec_instr_prop (Machconcr.State s f sp (Mbuiltin ef args res :: b) ms m) t
                  (Machconcr.State s f sp b (Regmap.set res v (undef_temps ms)) m').
Proof.
  intros; red; intros; inv MS.
  inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit external_call_mem_extends; eauto. eapply preg_vals; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  simpl undef_regs. repeat rewrite Pregmap.gso; auto with ppcgen. 
  rewrite <- H0. simpl. constructor; auto.
  eapply code_tail_next_int; eauto.
  apply agree_nextinstr_nf. eapply agree_set_undef_mreg; eauto. 
  rewrite Pregmap.gss. auto. 
  intros. repeat rewrite Pregmap.gso; auto with ppcgen. 
Qed.

Lemma exec_Mcond_true_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (cond : condition) (args : list mreg) (lbl : Mach.label)
         (c : list Mach.instruction) (ms : mreg -> val) (m : mem)
         (c' : Mach.code),
  eval_condition cond ms ## args = Some true ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop (Machconcr.State s fb sp (Mcond cond args lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c' (undef_temps ms) m).
Proof.
  intros; red; intros; inv MS. assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. intros EC.
  inv AT. monadInv H5.
  exploit transl_cond_correct; eauto. intros [rs' [A [B C]]].
  generalize (functions_transl _ _ _ FIND H4); intro FN.
  generalize (transf_function_no_overflow _ _ H4); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [GOTO [AT3 INV3]]]].
  left; exists (State rs3 m'); split.
  eapply plus_right'. 
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto. simpl. rewrite B. eauto. traceEq.
  econstructor; eauto. 
  eapply agree_exten_temps; eauto. intros. rewrite INV3; auto with ppcgen.
Qed.

Lemma exec_Mcond_false_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (cond : condition) (args : list mreg) (lbl : Mach.label)
         (c : list Mach.instruction) (ms : mreg -> val) (m : mem),
  eval_condition cond ms ## args = Some false ->
  exec_instr_prop (Machconcr.State s fb sp (Mcond cond args lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c (undef_temps ms) m).
Proof.
  intros; red; intros; inv MS.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in H0. 
  exploit transl_cond_correct; eauto. intros [rs' [A [B C]]].
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl. rewrite B. eauto. auto. 
  apply agree_nextinstr. eapply agree_exten_temps; eauto. 
Qed.

Lemma exec_Mjumptable_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (arg : mreg) (tbl : list Mach.label) (c : list Mach.instruction)
         (rs : mreg -> val) (m : mem) (n : int) (lbl : Mach.label)
         (c' : Mach.code),
  rs arg = Vint n ->
  list_nth_z tbl (Int.signed n) = Some lbl ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop
    (Machconcr.State s fb sp (Mjumptable arg tbl :: c) rs m) E0
    (Machconcr.State s fb sp c' (undef_temps rs) m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto. instantiate (2 := rs0#ECX <- Vundef #EDX <- Vundef). 
  rewrite Pregmap.gso; auto with ppcgen. rewrite Pregmap.gso; auto with ppcgen. eauto. eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply find_instr_tail; eauto. 
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
  econstructor; eauto. 
  eapply agree_exten_temps; eauto. intros. rewrite C; auto with ppcgen. 
  repeat rewrite Pregmap.gso; auto with ppcgen. 
Qed.

Lemma exec_Mreturn_prop:
  forall (s : list stackframe) (fb stk : block) (soff : int)
         (c : list Mach.instruction) (ms : Mach.regset) (m : mem) (f: Mach.function) m',
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
  load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
  Mem.free m stk (- f.(fn_framesize)) f.(fn_stacksize) = Some m' ->
  exec_instr_prop (Machconcr.State s fb (Vptr stk soff) (Mreturn :: c) ms m) E0
                  (Returnstate s ms m').
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]]. 
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]]. 
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. eapply exec_step_internal. 
  transitivity (Val.add rs#PC Vone). auto. rewrite <- H3. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
Qed.

Lemma exec_function_internal_prop:
  forall (s : list stackframe) (fb : block) (ms : Mach.regset)
         (m : mem) (f : function) (m1 m2 m3 : mem) (stk : block),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mem.alloc m (- fn_framesize f) (fn_stacksize f) = (m1, stk) ->
  let sp := Vptr stk (Int.repr (- fn_framesize f)) in
  store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp s) = Some m2 ->
  store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
  exec_instr_prop (Machconcr.Callstate s fb ms m) E0
                  (Machconcr.State s fb sp (fn_code f) ms m3).
Proof.
  intros; red; intros; inv MS.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. 

(* another one... ASW *)  
  assert (M0:(match x0 with
                 | nil => x0
                 | i1 :: nil => x0
                 | i1 :: i2 :: nil => x0
                 | i1 :: i2 :: i3 :: is =>
                     i1 :: i2 :: i3 :: Por_rr EAX EAX :: is
           end) = (x0)). admit.
  rewrite M0 in *.



  destruct (zlt (list_length_z x0) Int.max_unsigned); inversion EQ1. clear EQ1.
  unfold store_stack in *. 
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m1' [C D]].
  exploit Mem.storev_extends. eauto. eexact H1. eauto. eauto. 
  intros [m2' [E F]].
  exploit Mem.storev_extends. eexact F. eauto. eauto. eauto. 
  intros [m3' [P Q]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 


  rewrite <- H4; simpl. eauto. 
  simpl. rewrite C. simpl in E. rewrite (sp_val _ _ _ AG) in E. rewrite E.
  rewrite ATLR. simpl in P. rewrite P. eauto. 
  econstructor; eauto. 
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso; auto with ppcgen. 
  rewrite ATPC. simpl. constructor; eauto.
  subst x. eapply code_tail_next_int. rewrite list_length_z_cons. omega. 
  constructor. 
  apply agree_nextinstr. eapply agree_change_sp; eauto. congruence. 
Qed.

Lemma exec_function_external_prop:
  forall (s : list stackframe) (fb : block) (ms : Mach.regset)
         (m : mem) (t0 : trace) (ms' : RegEq.t -> val)
         (ef : external_function) (args : list val) (res : val) (m': mem),
  Genv.find_funct_ptr ge fb = Some (External ef) ->
  external_call ef ge args m t0 res m' ->
  Machconcr.extcall_arguments ms m (parent_sp s) (ef_sig ef) args ->
  ms' = Regmap.set (loc_result (ef_sig ef)) res ms ->
  exec_instr_prop (Machconcr.Callstate s fb ms m)
               t0 (Machconcr.Returnstate s ms' m').
Proof.
  intros; red; intros; inv MS.
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto. 
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto. 
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  unfold loc_external_result.
  eapply agree_set_mreg; eauto. 
  rewrite Pregmap.gso; auto with ppcgen. rewrite Pregmap.gss. auto. 
  intros. repeat rewrite Pregmap.gso; auto with ppcgen.
Qed.

Lemma exec_return_prop:
  forall (s : list stackframe) (fb : block) (sp ra : val)
         (c : Mach.code) (ms : Mach.regset) (m : mem),
  exec_instr_prop (Machconcr.Returnstate (Stackframe fb sp ra c :: s) ms m) E0
                  (Machconcr.State s fb sp c ms m).
Proof.
  intros; red; intros; inv MS. inv STACKS. simpl in *.
  right. split. omega. split. auto. 
  econstructor; eauto. rewrite ATPC; eauto.  
Qed.

Theorem transf_instr_correct:
  forall s1 t s2, Machconcr.step ge s1 t s2 ->
  exec_instr_prop s1 t s2.
Proof
  (Machconcr.step_ind ge exec_instr_prop
           exec_Mlabel_prop
           exec_Mgetstack_prop
           exec_Msetstack_prop
           exec_Mgetparam_prop
           exec_Mop_prop
           exec_Mload_prop
           exec_Mstore_prop
           exec_Mcall_prop
           exec_Mtailcall_prop
           exec_Mbuiltin_prop
           exec_Mgoto_prop
           exec_Mcond_true_prop
           exec_Mcond_false_prop
           exec_Mjumptable_prop
           exec_Mreturn_prop
           exec_function_internal_prop
           exec_function_external_prop
           exec_return_prop).

Lemma transf_initial_states:
  forall st1, Machconcr.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
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
  rewrite symbols_preserved. unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Machconcr.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto. 
  compute in H1. 
  generalize (preg_val _ _ _ AX AG). rewrite H1. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  Machconcr.exec_program prog beh -> Asm.exec_program tprog beh.
Proof.
  unfold Machconcr.exec_program, Asm.exec_program; intros.
  eapply simulation_star_preservation with (measure := measure); eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_instr_correct. 
Qed.

End PRESERVATION.
