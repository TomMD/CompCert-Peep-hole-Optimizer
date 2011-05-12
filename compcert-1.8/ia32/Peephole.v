
(* Add LoadPath "../common". *)
(* Add LoadPath "../backend". *)
(* Add LoadPath "../lib". *)
(* Add LoadPath "./standard". *)


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

Section Status_Dec.

Variable ge : genv.

Lemma int_eq_true : forall x y, Int.eq x y = true -> x = y.
Proof.
  intros.
  destruct (Int.eq_dec x y). trivial.  apply Int.eq_false in n. rewrite H in n. inversion n.
Qed.


Lemma eq_int_int__eq_z : forall x y, 
  @eq Int.int x y -> @eq Z (Int.unsigned x) (Int.unsigned y).
Proof.
  intros. f_equal. assumption.
Qed.

Lemma int_eq_false : forall x y, Int.eq x y = false -> x <> y.
Proof.
  intros. case_eq (Int.eq x y); intros.
  rewrite H0 in H. inversion H.
  unfold not. intro. unfold Int.eq in H0.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)). inversion H0. apply n.
  apply eq_int_int__eq_z. assumption.
Qed.

Definition val_eq (v1 v2 : val) : bool.
  refine (fun v1 v2 => 
    match v1 with
      | Vundef => match v2 with
                    | Vundef => true
                    | _ => false
                  end
      | Vint n => match v2 with
                    | Vint n' =>  Int.eq n n'
                    | _ => false
                  end
      | Vfloat n => match v2 with
                      | Vfloat n' => if Float.eq_dec n n' then true else false
                      | _ => false
                    end
      | Vptr b n => match v2 with 
                      | Vptr b' n' => if zeq b b' 
                        then Int.eq n n'
                        else false
                      | _ => false
                    end
    end). 
Defined.

Definition val_eq_dec (v1  v2 : val) : {v1 = v2} + {v1 <> v2}.
  refine (fun v1 v2 => (if val_eq v1 v2 as b return (val_eq v1 v2 = b -> {v1 = v2} + {v1 <> v2})
 then fun H : val_eq v1 v2 = true => Utils.in_left
 else fun H : val_eq v1 v2 = false => Utils.in_right)
  (refl_equal (val_eq v1 v2))). 

induction v1; induction v2; intros; simpl; try discriminate; try reflexivity. f_equal. apply int_eq_true. unfold val_eq in H. assumption.

unfold val_eq in *. case_eq (Float.eq_dec f f0); intros. f_equal. assumption. f_equal. rewrite H0 in H. inversion H. f_equal; unfold val_eq in *. destruct (zeq b b0). assumption. inversion H.
destruct (zeq b b0). apply int_eq_true. assumption.  inversion H.

induction v1; induction v2; intros; simpl; try discriminate; try reflexivity. unfold val_eq in *.
unfold Int.eq in *.  destruct (zeq(Int.unsigned i) (Int.unsigned i0)). inversion H. 
unfold not in *.
intro. apply n. f_equal. inversion H0. reflexivity.

unfold val_eq in H. case_eq (Float.eq_dec f f0); intros. rewrite H0 in H. inversion H.
unfold not. intros. apply n. inversion H1. reflexivity.

unfold val_eq in H. case_eq (zeq b b0).

intros. rewrite H0 in H. unfold not. intro. inversion H1.
apply int_eq_false in H. apply H. assumption.

intros. unfold not. intro. inversion H1. apply n. assumption.
Defined.

Eval simpl in (val_eq_dec Vundef Vundef).
Eval compute in (val_eq_dec Vundef Vundef).
Eval compute in (val_eq_dec Vundef Vzero).
(* appears to work *)


Theorem val_eq_correct : forall (v1 v2 : val), val_eq v1 v2 = true -> v1 = v2.
Proof.
  intro v1.
  intros.
  case_eq (val_eq_dec v1 v2). intros. assumption.
  intros. induction v1; induction v2; intros; try reflexivity; try discriminate. inversion H. 
  f_equal; apply int_eq_true; assumption.
  inversion H. destruct (Float.eq_dec f f0). f_equal; auto. inversion H2.
  inversion H.  destruct (zeq b b0); f_equal. assumption. apply int_eq_true. assumption.
  inversion H2. inversion H2.
Qed.
 


(* Issues raised in discussion with Xavier Leroy:

   PC -- as I suspected, the PC needs to be special cased in the
   comparison of states. Specifically we need to prove the semantic
   equivalence of the dereferencing of the PC, not it's value. This
   becomes particularly difficult if the PC is being stored in memory,
   because different PC values will show up in memory and we have no
   way to compare them at the value level. A memory entry that holds
   the PC could have a different value with the same semantic meaning,
   but how does one show that these are semantically equivalent.

   This is really only a problem with the addition or removal of
   instructions. Simple 1-to-1 instruction replacement is not a
   problem as the PC is not changed (modulo branching
   instructions). One solution, which would solve the case of
   instruction removal, is to *not* remove the instructions, but
   instead replace them with NOP until after the validation. This
   would leave the PC unchanged by the transformation. Subsequently,
   the NOPs could be removed and perhaps that transformation could be
   validated in a different manner --> forall instr in program, if
   instr != nop, instr in program', or some such. This does not solve
   the problem of inserting instructions.

   Another approach is to make the comparison between Mach and the
   transformed ASM instead of between two sets of ASM -- we could
   potentially reuse the existing proof structure to show
   equivalence. However, this doesn't work because the current proof
   is not a translation validation -- there is no infrastructure for
   comparing the semantics of the two levels directly. I'm not sure
   how tractable that problem is and whether it is feasible in the
   timeframe available.

*)

Definition reg_eq (r : preg) (rs1 rs2 : regset) : {rs1 r = rs2 r} + {rs1 r <> rs2 r}.
  refine (fun r rs1 rs2 => val_eq_dec (rs1 r) (rs2 r)).
Defined.

Notation "x &&& y" := (if x then if y then true else false else false).


Definition regs_eq (rs1 rs2 : regset) : bool.
  refine (fun rs1 rs2 =>  
    reg_eq PC rs1 rs2 &&&
    reg_eq ST0 rs1 rs2 &&&
    reg_eq RA rs1 rs2 &&&
    reg_eq EAX rs1 rs2 &&&
    reg_eq EBX rs1 rs2 &&&
    reg_eq ECX rs1 rs2 &&&
    reg_eq EDX rs1 rs2 &&&
    reg_eq ESI rs1 rs2 &&&
    reg_eq EDI rs1 rs2 &&&
    reg_eq EBP rs1 rs2 &&&
    reg_eq ESP rs1 rs2 &&&
    reg_eq XMM0 rs1 rs2 &&&
    reg_eq XMM1 rs1 rs2 &&&
    reg_eq XMM2 rs1 rs2 &&&
    reg_eq XMM3 rs1 rs2 &&&
    reg_eq XMM4 rs1 rs2 &&&
    reg_eq XMM5 rs1 rs2 &&&
    reg_eq XMM6 rs1 rs2 &&&
    reg_eq XMM7 rs1 rs2 &&&
    reg_eq ZF rs1 rs2 &&&
    reg_eq CF rs1 rs2 &&&
    reg_eq PF rs1 rs2 &&&
    reg_eq SOF rs1 rs2).
Defined.

Lemma if_falses : forall b : bool,
  (if b then false else false) = false.
Proof.
  intro b. induction b; auto.
Qed.

Theorem rs_eq__r_eq : forall  (r : preg) (rs1 rs2 : regset), 
  regs_eq rs1 rs2 = true -> rs1 r = rs2 r.
Proof.
  intro r. induction r; intros; unfold regs_eq in H.
  destruct (reg_eq PC rs1 rs2). auto. inversion H.

  induction i; intros;
  match goal with
    | |- ?RS1 ?R = ?RS2 _ => destruct (reg_eq R RS1 RS2)
  end; auto; rewrite if_falses in *; inversion H.

  induction f; intros;
  match goal with
    | |- ?RS1 ?R = ?RS2 _ => destruct (reg_eq R RS1 RS2)
  end; auto; rewrite if_falses in *; inversion H.
  
  destruct (reg_eq ST0 rs1 rs2). auto. destruct (reg_eq PC rs1 rs2); inversion H.

  induction c; intros;
  match goal with
    | |- ?RS1 ?R = ?RS2 _ => destruct (reg_eq R RS1 RS2)
  end; auto; rewrite if_falses in *; inversion H.

  destruct (reg_eq RA rs1 rs2). auto. rewrite if_falses in H. inversion H.
Qed.

Theorem rs_eq__r_eq2 : forall rs1 rs2,
  regs_eq rs1 rs2 = true -> forall r, rs1 r = rs2 r.
Proof.
  intros. induction r;
  apply rs_eq__r_eq; assumption.
Qed.

Lemma regs_eq__eq : forall rs1 rs2 : regset,
  regs_eq rs1 rs2 = true -> rs1 = rs2.
Proof.
  intros.
  assert (forall r, rs1 r = rs2 r).
  intros. apply rs_eq__r_eq. apply H. 
Require Import Coq.Logic.FunctionalExtensionality.
  apply functional_extensionality. assumption.
Qed.


Lemma reg_not_eq__regs_not_eq : forall rs1 rs2,
  (exists r, rs1 r <> rs2 r) -> regs_eq rs1 rs2 = false.
  intros.
  case_eq (regs_eq rs1 rs2).
  intros. inversion H. elimtype False.
  apply H1. apply rs_eq__r_eq. assumption.
  intros. reflexivity.
Qed.
  
Lemma regs_not_eq__not_eq : forall rs1 rs2 : regset,
  regs_eq rs1 rs2 = false -> exists r, rs1 r <> rs2 r.
Proof.
  intros.
  case_eq (regs_eq rs1 rs2). intros.
  rewrite H in H0. inversion H0.
  intros. clear H0.
  
  eexists.
  unfold not.
  intros. unfold regs_eq in H.
Admitted.
  

(*Inductive ireg: Type :=
  | EAX: ireg  | EBX: ireg  | ECX: ireg  | EDX: ireg
  | ESI: ireg  | EDI: ireg  | EBP: ireg  | ESP: ireg.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0: freg  | XMM1: freg  | XMM2: freg  | XMM3: freg
  | XMM4: freg  | XMM5: freg  | XMM6: freg  | XMM7: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register.  [SOF] is a pseudo-bit representing
  the "xor" of the [OF] and [SF] bits. *)

Inductive crbit: Type := 
  | ZF | CF | PF | SOF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)
*) 
  

(* work an example *)

Eval compute in (exec_instr ge nil (Pmov_rr EAX EBX) ((Pregmap.init Vundef)#EAX <- Vzero) Mem.empty).
Definition exec1 := 
  exec_instr ge
    nil 
    (Pmov_rr EAX EBX) 
    (((Pregmap.init Vundef)#EAX <- Vzero) # EBX <- Vzero)
    Mem.empty.

Definition exec2 := 
  exec_instr ge
    nil 
    (Pmov_rr EBX EAX) 
    (((Pregmap.init Vundef)#EAX <- Vzero) # EBX <- Vzero)
    Mem.empty.

Eval compute in (((Pregmap.init Vundef) # EAX <- Vzero) EAX).
Eval simpl in ((Pregmap.init Vundef) = (Pregmap.init Vundef)).

Lemma initregs_undef : forall r,
  (Pregmap.init Vundef) r = Vundef. 
Proof.
  intros. induction r; reflexivity.
Qed.

Example test : exec1 = exec2.
Proof.
  simpl. unfold exec1. unfold exec2. simpl. 
  remember ((((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero) # EAX <-
        (((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero EBX)).
  remember ((((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero) # EBX <-
        (((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero EAX)).
  f_equal. f_equal.
  apply regs_eq__eq.
  case_eq (regs_eq v v0).
  intros. reflexivity.
  intros.
 rewrite <- H.    
 apply regs_not_eq__not_eq in H. 
 inversion H.
 induction x.
 destruct (v PC). destruct (v0 PC). elimtype False. apply H0. reflexivity.
  

Admitted.

 (*  case_eq (regs_eq v v0).   *)
 (*  intros. (* need lemma -- regs_eq v v0 = true -> v = v0 to allow rewrite. *) *)
 (*  apply regs_eq__eq in H. rewrite H. reflexivity. *)
 (*  intro. *)
 (*  f_equal. *)
 (*  f_equal. *)
  


 (*  apply regs_eq__eq. *)
 (*  apply regs_not_eq__not_eq in H. inversion H.  *)
 (*  contradiction H0. *)
 (*  assert (regs_eq v v0 = true). *)

 (*  induction x. *)
 (*    case_eq (v PC). *)
 (*    intros. rewrite <- H1. *)
 (*  Eval compute in ((Pregmap.init Vundef) PC). *)
 (* destruct (v PC). destruct (v0 PC). reflexivity.  *)
  
  
  
End Status_Dec.

(* the initial register state for a program:

        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # RA <- Vzero
        # ESP <- (Vptr Mem.nullptr Int.zero) *)


(* Here I'll try again to show equivalence by assuming a fully
populated set of registers in a Section and see if it works. *)

Section test.

  (* the initial values for each register *)
  Variables eax ebx ecx edx esi edi ebp esp : val.
  Variables xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 : val.
  Definition init_regs := (Pregmap.init Vundef)
    # EAX <- eax
    # EBX <- ebx.

Eval simpl in (init_regs EAX). (* = init_regs EAX : val *)
Eval compute in (init_regs EAX). (* = eax : val *)
Eval compute in (init_regs # ECX <- ecx). (* = fun y : preg => if match ... *)
Eval compute in ((init_regs # ECX <- ecx) ECX). (* = ecx : val *)
Eval simpl in (Val.add eax ebx). (* = Val.add eax ebx *)
(* Eval simpl in (Val.add eax ebx). (* = FAILS TO TERMINATE, looking for real values?? *)*)

(* the above sort of blows things for this approach I think... *)

End test.

  

(*Inductive ireg: Type :=
  | EAX: ireg  | EBX: ireg  | ECX: ireg  | EDX: ireg
  | ESI: ireg  | EDI: ireg  | EBP: ireg  | ESP: ireg.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0: freg  | XMM1: freg  | XMM2: freg  | XMM3: freg
  | XMM4: freg  | XMM5: freg  | XMM6: freg  | XMM7: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register.  [SOF] is a pseudo-bit representing
  the "xor" of the [OF] and [SF] bits. *)

Inductive crbit: Type := 
  | ZF | CF | PF | SOF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)
*) 
