
Add LoadPath "../common".
Add LoadPath "../backend".
Add LoadPath "../lib".
Add LoadPath "./standard".


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

Definition val_eq_dec (v1 v2 : val) : {v1 = v2} + {v1 <> v2}.
Locate "{ _ } + { _ }".

  refine (fun v1 v2 => 
    match v1 with
      | Vundef => match v2 with
                    | Vundef => left _ _
                    | _ => right _ _
                  end
      | Vint n => match v2 with
                    | Vint n' => if Int.eq n n' then left _ _ else right _ _
                    | _ => right _ _
                  end
      | Vfloat n => match v2 with
                      | Vfloat n' => if Float.eq_dec n n' then left _ _ else right _ _
                      | _ => right _ _
                    end
      | Vptr b n => match v2 with 
                      | Vptr b' n' => if Int.eq_dec b b' then Int.eq_dec n n' else right _ _
                      | _ => right _ _
                    end
    end).

 case_eq (v1); case_eq v2. intros.auto. intros. right. auto. discriminate. intros. right. discriminate. intros. right. discriminate. right. discriminate. intros. 

Definition pregs_eq_dec (rs1 rs2 : regset) : {rs1 = rs2} + {rs1 <> rs2} :=
  rs1 EAX = rs2 EAX /\
  rs1 EBX = rs2 EBX.

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
