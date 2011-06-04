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
Require Import PeepholeLocations.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
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

Inductive SymOp :=
  | SymAdd
  | SymAddF
  | SymAnd
  | SymCmp
  | SymDivF
  | SymDivS
  | SymDivU
  | SymModS
  | SymModU
  | SymMult
  | SymMultF
  | SymOr
  | SymROR
  | SymShiftL
  | SymShiftR
  | SymShiftRU
  | SymSub
  | SymSubF
  | SymTest
  | SymXor.

Inductive SymExpr : Type :=
  (* Integers *)
  | binOp  : SymOp   -> SymExpr -> SymExpr -> SymExpr
  | neg    : SymExpr -> SymExpr

  (* Floating Operations *)
  | abs_f  : SymExpr -> SymExpr
  | neg_f  : SymExpr -> SymExpr
  | Imm    : val -> SymExpr
  | Initial : Loc -> SymExpr

  (* Memory *)
  | Load : addrmode -> list addrmode -> list SymExpr -> SymExpr.


(* we need a custom induction principle for our nested data type, a la cpdt *)
Section All.
 Variable T : Type.
 Variable P : T -> Prop.
  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | nil => True
      | h :: t => P h /\ All t
    end.
End All.

Implicit Arguments All.

Section SymExpr_ind'.
  Variable P : SymExpr -> Prop.

  Hypothesis binOp_case : forall (o : SymOp) (l : SymExpr),
    P l -> forall (r: SymExpr), P r -> P (binOp o l r).
  Hypothesis neg_case : forall (l : SymExpr),
    P l -> P (neg l).
  Hypothesis abs_f_case : forall (l : SymExpr),
    P l -> P (abs_f l).
  Hypothesis neg_f_case : forall (l : SymExpr),
    P l -> P (neg_f l).
  Hypothesis Imm_case : forall l, P (Imm l).
  Hypothesis Initial_case : forall l, P (Initial l).

  Hypothesis Load_case : forall (a : addrmode) (la : list addrmode) (le : list SymExpr),
    All P le -> P (Load a la le).

  Fixpoint SymExpr_ind' (s : SymExpr) : P s :=
    match s as s' return P s' with
      | binOp o l r => binOp_case o l (SymExpr_ind' l) r (SymExpr_ind' r)
      | neg l => neg_case l (SymExpr_ind' l)
      | abs_f l => abs_f_case l  (SymExpr_ind' l)
      | neg_f l => neg_f_case l (SymExpr_ind' l)
      | Imm l => Imm_case l
      | Initial l => Initial_case l
      | Load a la le => Load_case a la le
        ((fix list_SymExp (ls : list SymExpr) : All P ls :=
        match ls with
          | nil => I
          | s :: ss => conj (SymExpr_ind' s) (list_SymExp ss)
        end) le)
    end.

End SymExpr_ind'.



Definition cmp := binOp SymCmp.
Definition test := binOp SymTest.
Definition add := binOp SymAdd.
Definition sub := binOp SymSub.
Definition mult := binOp SymMult.
Definition div_unsigned := binOp SymDivU.
Definition div_signed := binOp SymDivS.
Definition mod_unsigned := binOp SymModU.
Definition mod_signed := binOp SymModS.
Definition shiftL := binOp SymShiftL.
Definition shiftR := binOp SymShiftR.
Definition shiftR_unsigned := binOp SymShiftRU.
Definition ror := binOp SymROR.
Definition and := binOp SymAnd.
Definition or := binOp SymOr.
Definition xor := binOp SymXor.
Definition add_f := binOp SymAddF.
Definition sub_f := binOp SymSubF.
Definition mult_f := binOp SymMultF.
Definition div_f := binOp SymDivF.

Inductive Constraint : Type :=
  | ReadMem  : addrmode -> Constraint
  | WriteMem : addrmode -> Constraint
  | DivBy    : SymExpr  -> Constraint.

Definition addrmode_eq : forall (a1 a2 : addrmode), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality.  decide equality. apply Int.eq_dec. decide equality.
  apply Int.eq_dec. apply ident_eq.
  decide equality. decide equality. apply Int.eq_dec.
  apply ireg_eq.
  decide equality. apply ireg_eq.
Defined.

Definition beq_addrmode (a b : addrmode) : bool :=
  match addrmode_eq a b with
    | left _ => true
    | right _ => false
  end.

(* to decide equality of symbolic expressions, we need to decide equality of values *)
Definition val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality ; try apply Int.eq_dec.
  apply Float.eq_dec.  apply eq_block.
Defined.

Definition beq_val (a b : val) : bool :=
  match val_eq_dec a b with
    | left _ => true
    | right _ => false
  end.

(* define equality for Loc, used in the Loc store *)
Lemma Loc_eq : forall (x y : Loc), {x = y} +  {x <> y}.
Proof.
  decide equality. 
  apply preg_eq.
  repeat decide equality; try apply Int.eq_dec.
Defined.

Definition beq_Loc (a b : Loc) : bool :=
  match Loc_eq a b with
    | left _ => true
    | right _ => false
  end.

(* decide equality for symbolic operators *)
Lemma SymOp_eq : forall (x y : SymOp), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition beq_SymOp (a b : SymOp) : bool :=
  match SymOp_eq a b with
    | left _ => true
    | right _ => false
  end.

(* decide equality for symbolic expressions. note this is *syntactic* equality
Definition SymExpr_dec : forall (a b : SymExpr), {a = b} + {a <> b}.
  let MemState_Eq := fix MemState_Eq (f1 f2 : MemState) :=
    match f1,f2 as _ with
      | nil,nil => left _
      | nil,_   => right _
      | _,nil   => right _
      | (a1,e1)::xs, (a2,e2)::ys => SymExpr_dec e1 e2 /\ addrmode_eq a1 a2
    end
  in decide equality.
Admitted.

Definition beq_SymExpr (s1 s2 : SymExpr) : bool :=
  match SymExpr_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.
*)

Fixpoint beq_SymExpr (s1 s2 : SymExpr) : bool :=
  let leq_SE := fix leq_SE (x1 x2 : list SymExpr) :=
    match x1, x2 with
      | nil, nil => true
      | x::xs, y::ys => beq_SymExpr x y && leq_SE xs ys
      | _, _  => false
    end in
    let leq_AM := fun l1 l2 =>
      if list_eq_dec addrmode_eq l1 l2
        then true
        else false in
    match s1, s2 with
      | binOp o1 e11 e12, binOp o2 e21 e22 => beq_SymOp o1 o2 && beq_SymExpr e11 e21 
        && beq_SymExpr e12 e22
      | neg e1, neg e2 => beq_SymExpr e1 e2
      | abs_f e1, abs_f e2 => beq_SymExpr e1 e2
      | neg_f e1, neg_f e2 => beq_SymExpr e1 e2
      | Imm v1, Imm v2 => beq_val v1 v2
      | Initial l1, Initial l2 => beq_Loc l1 l2
      | Load a1 as1 es1, Load a2 as2 es2 => leq_AM as1 as2 && leq_SE es1 es2 && beq_addrmode a1 a2
      | _,_ => false
    end.

(*
Definition constraint_eq : forall (c1 c2 : Constraint), {c1 = c2} + {c1 <> c2}.
Proof.
 decide equality. apply addrmode_eq. apply addrmode_eq. apply SymExpr_dec.
Defined.
*)

Definition beq_constraint (a b : Constraint) : bool :=
  match a, b with
    | ReadMem a1, ReadMem a2 => beq_addrmode a1 a2
    | WriteMem a1, WriteMem a2 => beq_addrmode a1 a2
    | DivBy e1, DivBy e2 => beq_SymExpr e1 e2
    | _, _ => false
  end.

(* the type of our memory store *)
Definition mems := @LocStore addrmode SymExpr addrmode_eq.

(* the type of our register store *)
Definition regs := @LocStore preg SymExpr preg_eq.

(* A "SymState" encodes the concept of the state of a symbolic execution.
   It includes a mapping of locations to symbolic expressions and set
   of contraints (operations that could cause exceptions or other bad behavior).

  While "mems" and "regs" are the same type (sort of), the difference
  is how they're used.  mems are keyed by locations (addrmode's) which
  might alias while regs are keyed by registers which we know don't
  alias.  *)
Inductive SymState := SymSt : list Constraint -> mems -> regs -> SymState.

(* Helper functions & notation to modify the 'locs' of a SymState *)
Definition symMem (s : SymState) : mems :=
  match s with
  | SymSt _ l _ => l
  end.

Definition symReg (s : SymState) : regs :=
  match s with
  | SymSt _ _ l => l
  end.

Definition symSetMem (l : addrmode) (x : SymExpr) (s : SymState) : SymState :=
  match s with
  | SymSt c m r => SymSt c (update l  x m) r
  end.

Definition symSetReg (l : preg) (x : SymExpr) (s : SymState) : SymState :=
  match s with
  | SymSt c m r => SymSt c m (update l x r)
  end.

Definition constraints (s : SymState) : list Constraint :=
  match s with
  | SymSt c _ _ => c
  end.

(* Helper functions to modify the constraints of a SymState *)
Definition readMem  (l : addrmode) (s : SymState) : SymState :=
  match s with
    | SymSt c mapping r => SymSt (ReadMem l::c) mapping r
  end.

Definition writeMem (l : addrmode) (s : SymState) : SymState :=
  match s with
    | SymSt c mapping r => SymSt (WriteMem l ::c) mapping r
  end.

Definition divBy (e : SymExpr) (s : SymState) : SymState :=
  match s with
    | SymSt c mapping r => SymSt (DivBy e :: c) mapping r
  end.

(** the initial state of our symbolic store returns the initial value
    for a given location. This means that no location is initially
    undefined and instead has the value "Initial foo" for the location
    "foo". Not sure why I have to restate the decision procedure, but
    there it is *)
Definition initMem : mems := initLocStore addrmode_eq (compose Initial Memory).
Definition initReg : regs := initLocStore preg_eq (compose Initial Register).
Definition initSymSt : SymState := SymSt nil initMem initReg.

Fixpoint unzip {A B : Type} (ps : list (A*B)) : (list A * list B) :=
  match ps with
    | nil => (nil, nil)
    | (a, b) :: ps' => let (as',bs') := unzip ps' in (a :: as', b :: bs')
  end.

Notation "a # b" :=
  match b with
  | Register p => (lookup p (symReg a))
  | Memory m   => let (addrs,syms) := unzip (store (symMem a)) in 
    Load m addrs syms  (* (lookup m (symMem a)) *)
  end (at level 1, only parsing).

Notation "a # b <- c" :=
  match b with
  | Register p => (symSetReg p c a)
  | Memory m   => (symSetMem m c a )
  end (at level 1, b at next level).

Definition eval_addrmode (a: addrmode) (l : SymState) : option SymExpr :=
  match a with Addrmode base ofs const =>
    match const with
      | inr (id, ofs') => None
      | inl ofs' => Some
        (add (match base with
               | None => (Imm Vzero)
               | Some r => (l # (Register r))
             end)
        (add (match ofs with
                | None => (Imm Vzero)
                | Some(r, sc) =>
                  if Int.eq sc Int.one 
                    then (l # (Register r)) 
                    else (mult (l # (Register r)) (Imm (Vint sc)))
              end)
        (Imm (Vint ofs'))))
    end
  end.

Definition symUndef := Imm Vundef.

Definition setAllFlags (l : SymState) (e : SymExpr) : SymState :=
  l # (Register (CR ZF))  <- e
    # (Register (CR CF))  <- e
    # (Register (CR PF))  <- e
    # (Register (CR SOF)) <- e.

(* small step symbolic execution *)
Definition single_symExec (i : instruction) (l : SymState) : option SymState :=
  match i with
  | Pnop => Some l
      (** Moves *)
  | Pmov_rr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmov_ri rd n =>
      Some (l # (Register rd) <- (Imm (Vint n)))
  | Pmov_rm rd a =>
      Some (readMem a (l # (Register rd) <- (l # (Memory a))))
  | Pmov_mr a r1 =>
      Some (writeMem a (l # (Memory a) <- (l # (Register r1))))
  | Pmovd_fr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovd_rf rd r1 => 
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_ff rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_fi rd n =>
      Some (l # (Register rd) <- (Imm (Vfloat n))) 
  | Pmovsd_fm rd a =>
      Some (readMem a (l # (Register rd) <- (l # (Memory a))))
  | Pmovsd_mf a r1 =>
      Some (writeMem a (l # (Memory a) <- (l # (Register r1))))
  | Pfld_f r1 =>
      Some (l # (Register ST0) <- (l # (Register r1)))  (* We don't track flags for the FPU *)
  | Pfld_m a =>
      Some (writeMem a (l # (Memory a) <- (l # (Register ST0))))
  | Pfstp_f rd =>
      Some (l # (Register rd) <- (l # (Register ST0)))
  | Pfstp_m a =>
      Some (writeMem a (l # (Memory a) <- (l # (Register ST0))))
  (** Moves with conversion -- Currently unsupported *)
  | Pmovb_mr a r1 =>
      None (* exec_store Mint8unsigned m a rs r1 *)
  | Pmovw_mr a r1 =>
      None (*  exec_store Mint16unsigned m a rs r1 *)
  | Pmovzb_rr rd r1 =>
      None (*  Some ( (l # (Register rd) <- (Val.zero_ext 8 rs#r1))) m *)
  | Pmovzb_rm rd a =>
      None (* exec_load Mint8unsigned m a rs rd *)
  | Pmovsb_rr rd r1 =>
      None (* Some ( (l # (Register rd) <- (Val.sign_ext 8 rs#r1))) m *)
  | Pmovsb_rm rd a =>
      None (* exec_load Mint8signed m a rs rd*)
  | Pmovzw_rr rd r1 =>
      None (* Some (l # (Register rd) <- (Val.zero_ext 16 rs#r1))) m *)
  | Pmovzw_rm rd a =>
      None (* exec_load Mint16unsigned m a rs rd*)
  | Pmovsw_rr rd r1 =>
      None (* Some (l # (Register rd) <- (Val.sign_ext 16 rs#r1))) m *)
  | Pmovsw_rm rd a =>
      None (* exec_load Mint16signed m a rs rd*)
  | Pcvtss2sd_fm rd a =>
      None (* exec_load Mfloat32 m a rs rd*)
  | Pcvtsd2ss_ff rd r1 =>
      None (* Some (l # (Register rd) <- (Val.singleoffloat rs#r1))) m *)
  | Pcvtsd2ss_mf a r1 =>
      None (*exec_store Mfloat32 m a rs r1*)
  | Pcvttsd2si_rf rd r1 =>
      None (* Some (l # (Register rd) <- (Val.intoffloat rs#r1))) m *)
  | Pcvtsi2sd_fr rd r1 =>
      None (* Some (l # (Register rd) <- (Val.floatofint rs#r1))) m *)
  (** Integer arithmetic *)
  | Plea rd a =>
      (* FIXME!! not sure Imm eval_addrmode is right *)
    match eval_addrmode a l with
      | Some v => Some (l # (Register rd) <- v)
      | None => None
    end
  | Pneg rd =>
    let res := neg (l # (Register rd)) in
      Some (setAllFlags (l # (Register rd) <- res) res)
  | Psub_rr rd r1 =>
    let res := sub (l # (Register rd)) (l # (Register r1)) in
      Some (setAllFlags (l # (Register rd) <- (sub (l # (Register rd)) (l # (Register r1)))) res)
  | Pimul_rr rd r1 =>
    let res := mult (l # (Register rd)) (l # (Register r1)) in
      Some (l # (Register rd) <- res
              # (Register (CR ZF)) <- symUndef
              # (Register (CR PF)) <- symUndef
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- symUndef (* OF is actually set while SF is undef on x86 *)
              )
  | Pimul_ri rd n =>
    let res := mult (l # (Register rd)) (Imm (Vint n)) in
      Some (l # (Register rd) <- res
              # (Register (CR ZF)) <- symUndef
              # (Register (CR PF)) <- symUndef
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- symUndef (* OF is actually set while SF is undef on x86 *)     
           )
  | Pdiv r1 =>
      let r1Val := (l # (Register EDX) <- (Imm Vundef)) # (Register r1) in
      Some (divBy r1Val (setAllFlags (l
        # (Register EAX) <- 
          (div_unsigned (l # (Register EAX)) r1Val)
        # (Register EDX) <- 
          (mod_unsigned (l # (Register EAX)) r1Val)) symUndef))
  | Pidiv r1 =>
     let r1Val := (l # (Register EDX) <- (Imm Vundef)) # (Register r1) in
      Some (divBy r1Val (setAllFlags (l 
        # (Register EAX) <- 
          (div_signed (l # (Register EAX)) r1Val)) 
        # (Register EDX) <- 
          (mod_signed (l # (Register EAX)) r1Val) symUndef))
  | Pand_rr rd r1 =>
    let res := and (l # (Register rd)) (l # (Register r1)) in
      Some (l # (Register rd) <- res
              # (Register (CR SOF)) <- res  (* OF is cleared, but we can't capture that *)
              # (Register (CR CF)) <- (Imm (Vint (Int.repr 0)))
              # (Register (CR ZF)) <- res
              # (Register (CR PF)) <- res)
  | Pand_ri rd n =>
    let res := and (l # (Register rd)) (Imm (Vint n)) in
      Some (l # (Register rd) <- res
              # (Register (CR SOF)) <- res  (* OF is cleared, but we can't capture that *)
              # (Register (CR CF)) <- (Imm (Vint (Int.repr 0)))
              # (Register (CR ZF)) <- res
              # (Register (CR PF)) <- res)
  | Por_rr rd r1 =>
      Some (l # (Register rd) <- (or (l # (Register rd)) (l # (Register r1))))
  | Por_ri rd n =>
      Some (l # (Register rd) <- (or (l # (Register rd)) (Imm (Vint n))))
  | Pxor_rr rd r1 =>
      Some (l # (Register rd) <- (xor (l # (Register rd)) (l # (Register r1))))
  | Pxor_ri rd n =>
      Some (l # (Register rd) <- (xor (l # (Register rd)) (Imm (Vint n))))
  | Psal_rcl rd =>
    let res := shiftL (l # (Register rd)) (l # (Register ECX)) in
      Some (l # (Register rd) <- res
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- res)
  | Psal_ri rd n =>
    let res := shiftL (l # (Register rd)) (Imm (Vint n)) in
      Some (setAllFlags (l # (Register rd) <- res) res)
  | Pshr_rcl rd =>
    let res := shiftR_unsigned (l # (Register rd)) (l # (Register ECX)) in
      Some (l # (Register rd) <- res
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- res)
  | Pshr_ri rd n =>
    let res := shiftR_unsigned (l # (Register rd)) (Imm (Vint n)) in
      Some (setAllFlags (l # (Register rd) <- res) res)
  | Psar_rcl rd =>
    let res := shiftR (l # (Register rd)) (l # (Register ECX)) in
      Some (l # (Register rd) <- res
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- res)
  | Psar_ri rd n =>
    let res := shiftR (l # (Register rd)) (Imm (Vint n)) in
      Some (setAllFlags (l # (Register rd) <- res) res)
  | Pror_ri rd n =>
    let res := ror (l # (Register rd)) (Imm (Vint n)) in
      Some (l # (Register rd) <- res
              # (Register (CR CF)) <- res
              # (Register (CR SOF)) <- res)
  | Pcmp_rr r1 r2 =>
      let res := cmp (l # (Register r1)) (l # (Register r2)) in
        Some (setAllFlags l res)
  | Pcmp_ri r1 n =>
      Some (setAllFlags l (cmp (l # (Register r1)) (Imm (Vint n))))
  | Ptest_rr r1 r2 =>
      let res := test (l # (Register r1)) (l # (Register r2)) in
        Some (l # (Register (CR CF))  <- (Imm (Vint (Int.repr 0)))
                # (Register (CR SOF)) <- res
                # (Register (CR ZF))  <- res
                # (Register (CR PF))  <- res)
  | Ptest_ri r1 n =>
      let res := test (l # (Register r1)) (Imm (Vint n)) in
        Some (l # (Register (CR CF))  <- (Imm (Vint (Int.repr 0)))
                # (Register (CR SOF)) <- res
                # (Register (CR ZF))  <- res
                # (Register (CR PF))  <- res)
  | Pcmov c rd r1 =>
     None (*
     (* FIXME!! needs rewrite of eval_testcond *)
      match eval_testcond c rs with
      | Some true => Some (l # (Register rd) <- (l # (Register r1)))
      | Some false => Some l
      | None => None
      end*)
  | Psetcc c rd =>
      None (*
     (* FIXME!! needs rewrite of eval_testcond *)
      match eval_testcond c rs with
      | Some true => Some ((l # (Register ECX) <- (Imm Vundef)) # (Register EDX) <- (Imm Vundef))
                          #  (Register rd) <- (Imm Vtrue)
      | Some false => Some (l # (Register ECX) <- (Imm Vundef)) # (Register rd) <- (Imm Vfalse)
      | None => None
      end *)
  (** Arithmetic operations over floats *)
  | Paddd_ff rd r1 =>
      Some (l # (Register rd) <- (add_f (l # (Register rd)) (l # (Register r1))))
  | Psubd_ff rd r1 =>
      Some (l # (Register rd) <- (sub_f (l # (Register rd)) (l # (Register r1))))
  | Pmuld_ff rd r1 =>
      Some (l # (Register rd) <- (mult_f (l # (Register rd)) (l # (Register r1))))
  | Pdivd_ff rd r1 =>
      Some (l # (Register rd) <- (div_f  (l # (Register rd)) (l # (Register r1))))
  | Pnegd rd =>
      Some (l # (Register rd) <- (neg_f (l # (Register rd))))
  | Pabsd rd =>
      Some (l # (Register rd) <- (abs_f (l # (Register rd))))
  | Pcomisd_ff r1 r2 =>
      None (*Some ( (compare_floats (rs r1) (rs r2) rs)) m*)
  (** Branches and calls *)
  | Pjmp_l lbl =>
      None (* goto_label c lbl rs m*)
  | Pjmp_s id =>
      None (* Next (rs#PC <- (symbol_offset id Int.zero)) m*)
  | Pjmp_r r =>
      None (* Next (rs#PC <- (rs r)) m*)
  | Pjcc cond lbl =>
      None (*
      match eval_testcond cond rs with
      | Some true => goto_label c lbl rs m
      | Some false => Some ( rs) m
      | None => Stuck
      end *)
  | Pjmptbl r tbl =>
      None (*
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.signed n) with
          | None => Stuck
          | Some lbl => goto_label c lbl (rs #ECX <- Vundef #EDX <- Vundef) m
          end
      | _ => Stuck
      end *)
  | Pcall_s id =>
      None (*
      Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (symbol_offset id Int.zero)) m*)
  | Pcall_r r =>
      None (*
      Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (rs r)) m *)
  | Pret =>
      None (*
      Next (rs#PC <- (rs#RA)) m *)
  (** Pseudo-instructions *)
  | Plabel lbl =>
      None (*
      Some ( rs) m *)
  | Pallocframe lo hi ofs_ra ofs_link =>
      None (*
      let (m1, stk) := Mem.alloc m lo hi in
      let sp := Vptr stk (Int.repr lo) in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with
      | None => Stuck
      | Some m2 =>
          match Mem.storev Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with
          | None => Stuck
          | Some m3 => Some ( (rs#ESP <- sp)) m3
          end
      end *)
  | Pfreeframe lo hi ofs_ra ofs_link =>
      None (*
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => Stuck
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk lo hi with
                  | None => Stuck
                  | Some m' => Some ( (rs#ESP <- sp #RA <- ra)) m'
                  end
              | _ => Stuck
              end
          end
      end *)
  | Pbuiltin ef args res =>
      None
      (* Stuck                             (**r treated specially below *)*)
  end.

Fixpoint symExec (c : code) (l : SymState) : option SymState :=
  match c with
    | nil => Some l
    | i :: is => match (single_symExec i l) with
                   | Some l' => symExec is l'
                   | None => None
                 end
  end.

Notation "a '&&&' b" := 
  (if a 
    then if b
      then Utils.in_left
      else Utils.in_right
    else Utils.in_right).

(*
Fixpoint allLocs_dec (l : list Loc) (a b : SymState) : bool :=
  match l with
    | nil => true
    | l' :: ls => 
      if SymExpr_dec (a # l') (b # l') 
        then allLocs_dec ls a b
        else false
  end.
*)

Definition isCR (c : preg) : bool :=
  match c with
    | (CR _) => true
    | _ => false
  end.

Fixpoint all {A : Type} (p : A -> bool) (xs : list A) : bool :=
  match filter (fun x => negb (p x)) xs with
    | nil => true
    | _   => false
  end.

(* Begin Stubs! *)
(* Test if 'a' is a subset of 'b' *)
Fixpoint subset (a b : list Constraint) : bool :=
  match a with
    | nil => true
    | (x::xs) => existsb (fun z => beq_constraint z x) b && subset xs b (* fixme direct eq isn't quite right *)
  end.

Fixpoint normalizeSymOp (o : SymOp) (e1 e2 : SymExpr) : SymExpr := binOp o e1 e2.

Definition nonaliasedLookup (a : addrmode) (addrs : list addrmode)(syms : list SymExpr) : SymExpr :=
  Load a addrs syms.

Fixpoint normalizeMem (addrs : list addrmode) (syms : list SymExpr) : (list addrmode * list SymExpr) := (addrs, syms).

Fixpoint normalize (s : SymExpr) : SymExpr :=
  match s with
    | binOp o e1 e2 =>
      let d1 := normalize e1 in let d2 := normalize e2 in
        normalizeSymOp o d1 d2
    | neg e =>
        match e with
          | neg x => normalize x
          | _     => normalize e
        end
    | abs_f e =>
        match e with
          | abs_f x => abs_f (normalize x)
          | _       => abs_f (normalize e)
        end
    | neg_f e =>
        match e with
          | neg_f x => normalize x
          | _       => normalize e
        end
    | Imm v => Imm v
    | Initial l => Initial l
    | Load a addrs syms => let (addrs', syms') := normalizeMem addrs syms
      in nonaliasedLookup a addrs' syms'
  end.

Definition validMem (c : SymState) (d : SymState) : bool := false.

Definition validRegs (l : list preg) (c d : SymState) : bool := false.
(* End stubs (I hope) *)

Definition validFlag (f : Loc) (c : SymState) (d : SymState) : bool :=
  beq_SymExpr (c # f) symUndef || beq_SymExpr (c # f) (d # f).

(* A valid flag is one with the same definition or one that becomes
  "more defined" from a previous symUndef value. *)
Definition validFlags (c : SymState) (d : SymState) : bool :=
  validFlag (Register (CR ZF)) c d && 
  validFlag (Register (CR PF)) c d && 
  validFlag (Register (CR CF)) c d && 
  validFlag (Register (CR SOF)) c d.

Definition sameSymbolicExecution (c : option SymState) (d : option SymState) : bool :=
  match c, d with
    | Some c', Some d' =>
      let regC := filter (fun x => negb (isCR x)) (elements (symReg c')) in
        let regD := filter (fun x => negb (isCR x)) (elements (symReg d')) in
          validFlags c' d' &&
          validRegs  (regC ++ regD) c' d' &&
          validMem c' d'
    | _, _ => false
  end.

(** peephole_validate validates the code optimized by the untrusted
  optimizer is semantically correct.  We only need to prove that
  peephole_validate returns true only when the two inputs are
  semantically correct.  It would be nice to have a proof that it
  doesn't return false given certain known-correct conditions, but
  that isn't required.
 *)
Fixpoint peephole_validate (c : Asm.code) (d : Asm.code) : bool :=
  if (negb (beq_nat (length c) 0)) && Compare_dec.leb (length d) (length c)
    then sameSymbolicExecution (symExec c initSymSt) (symExec d initSymSt)    
    else false.

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

Lemma skipn_single_S (A : Type) : forall (a : A) l n,
  ((length (skipn (Datatypes.S n) (a::l))) = (length (skipn n l))).
Proof.
  auto.
Qed.

Lemma skipn_S  (A : Type ): forall (l :list A) n,
  ((length (skipn (Datatypes.S n) l)) <= (length (skipn n l)))%nat.
Proof.
  intros.
  generalize dependent l.
  induction n.
  intros. destruct l. auto. simpl. auto.
  intros.
  destruct l. simpl. auto.
  rewrite skipn_single_S. rewrite skipn_single_S.
  apply IHn. 
Qed.

Lemma skipn_le (A : Type) : forall n (l :list A),
  ((length (skipn n l)) <= length l)%nat.
Proof.
  induction n.
  auto.
  intros.
  assert ((length (skipn (Datatypes.S n) l)) <= (length (skipn n l)))%nat by apply skipn_S.
  eapply le_trans. apply H. apply IHn.
Qed.  

Fixpoint only_opt_instrs (c : code) : code :=
  match c with 
    | nil => nil
    | x :: xs => match (single_symExec x initSymSt) with
                   | None => nil
                   | Some _ => x :: only_opt_instrs xs 
                 end
  end.

Function basic_block (c : Asm.code) {measure length c} : list Asm.code :=
  match c with
    | nil => nil
    | x :: xs => match (single_symExec x initSymSt) with
                   | None => (x :: nil) :: (basic_block xs) (* singleton of unoptimized instr *)
                   | Some _ => let opts := only_opt_instrs xs 
                     in (x :: opts) :: basic_block (skipn (length opts) xs)
                 end
  end.
  intros. simpl.
  apply le_lt_n_Sm. apply skipn_le.
  auto.
Qed.

Definition concat (c : list Asm.code) : Asm.code := fold_left (fun a b => a ++ b) c nil.

Definition optimize (c : Asm.code) : Asm.code :=
  let parts := basic_block c in concat (map opt_window parts).
    
Definition transf_function (f: Asm.code) : res Asm.code :=
  OK (optimize f).

Definition transf_fundef (f : Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition peephole_transf_program (p : Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.