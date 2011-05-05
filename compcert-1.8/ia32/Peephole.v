
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

Definition regs_eq (rs1 rs2 : regset) : bool.
  refine (fun rs1 rs2 => 
  if val_eq_dec (rs1 PC) (rs2 PC) 
    then if val_eq_dec (rs1 (IR EAX)) (rs2 (IR EAX))
      then true
      else false
    else false).
Defined.

Theorem rs_eq__r_eq : forall (r : preg) (rs1 rs2 : regset), regs_eq rs1 rs2 = true -> rs1 r = rs2 r.
Proof.
  intro r. induction r.
  intros. unfold regs_eq in H. destruct (val_eq_dec (rs1 PC) (rs2 PC)). assumption. inversion H.

(* what does the equal sign mean here? In other words, how do we specify that two PCs are equivalent? *)

Inductive pc_equiv :=
| 

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
  

(* Here we attempt to define equality of register sets. Two registers
sets, rs1 rs2, are equivalent if (for all R : preg, R <> PC, rs1 R =
rs2 R) /\ rs1 PC equiv rs2 PC) for some equivalence relation on the
dereference of PCs. *)


Theorem test : exec1 = exec2.
simpl. unfold exec1. unfold exec2. simpl. 

assert (H:(((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero) # EAX <-
        (((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero EBX) =
        (((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero) # EBX <-
        (((Pregmap.init Vundef) # EAX <- Vzero) # EBX <- Vzero EAX)).
(* need an equality relation on registers *).


(* the initial register state for a program:

        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # RA <- Vzero
        # ESP <- (Vptr Mem.nullptr Int.zero) *)
