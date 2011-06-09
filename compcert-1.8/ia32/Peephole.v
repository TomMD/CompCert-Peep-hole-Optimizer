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

(* The binary operations were extracted to make the proof of
   equality decidability have notably fewer cases, finish faster *)
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
  | InitialReg : preg -> SymExpr
  | InitialMem : SymExpr -> SymExpr

  (* Memory *)
  | Load : SymExpr -> list SymExpr -> list SymExpr -> SymExpr. (* addr being read, addr of value, value stored  *)

(* To try and avoid confusion we use the alias 'Addr' to refer to
  SymExprs that represent an address *)
Definition Addr := SymExpr.

Inductive Loc : Type :=
  | Register : preg -> Loc
  | Memory   : Addr -> Loc.

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
  Hypothesis InitialReg_case : forall l, P (InitialReg l).
  Hypothesis InitialMem_case : forall l, P l -> P (InitialMem l).

  Hypothesis Load_case : forall (a : Addr) (la : list SymExpr) (le : list SymExpr),
    P a -> All P la -> All P le -> P (Load a la le).

  Fixpoint SymExpr_ind' (s : SymExpr) : P s :=
    let list_SymExpr := (fix list_SymExpr (l : list SymExpr) : All P l :=
        match l  with
          | nil => I
          | h :: t  => conj (SymExpr_ind' h) (list_SymExpr t)
        end) in
    match s as s' return P s' with
      | binOp o l r => binOp_case o l (SymExpr_ind' l) r (SymExpr_ind' r)
      | neg l => neg_case l (SymExpr_ind' l)
      | abs_f l => abs_f_case l  (SymExpr_ind' l)
      | neg_f l => neg_f_case l (SymExpr_ind' l)
      | Imm l => Imm_case l
      | InitialReg l => InitialReg_case l
      | InitialMem l => InitialMem_case l (SymExpr_ind' l)
      | Load addr la le => Load_case addr la le (SymExpr_ind' addr)
        (list_SymExpr la) (list_SymExpr le)
    end.

End SymExpr_ind'.

(* helper functions to construct SymExpr's in the obvious way *)
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

(* Constraints are any side-effecting operation (e.g. potentially causing an exception) *)
Inductive Constraint : Type :=
  | ReadMem  : SymExpr -> Constraint
  | WriteMem : SymExpr -> Constraint
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
Definition val_eq : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}.
Proof.
  decide equality ; try apply Int.eq_dec.
  apply Float.eq_dec.  apply eq_block.
Defined.

Definition beq_val (a b : val) : bool :=
  match val_eq a b with
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

Definition beq_preg (a b : preg) : bool :=
  match preg_eq a b with
    | left _ => true
    | right _ => false
  end.

Definition beq_list_preg (a b : list preg) : bool :=
  fold_left andb (map (fun p => beq_preg (fst p) (snd p)) (combine a b)) true.

Fixpoint beq_SymExpr (s1 s2 : SymExpr) : bool :=
  let leq_SE := fix leq_SE (x1 x2 : list SymExpr) :=
    match x1, x2 with
      | nil, nil => true
      | x::xs, y::ys => beq_SymExpr x y && leq_SE xs ys
      | _, _  => false
    end in
    match s1, s2 with
      | binOp o1 e11 e12, binOp o2 e21 e22 => beq_SymOp o1 o2 && beq_SymExpr e11 e21 
        && beq_SymExpr e12 e22
      | neg e1, neg e2 => beq_SymExpr e1 e2
      | abs_f e1, abs_f e2 => beq_SymExpr e1 e2
      | neg_f e1, neg_f e2 => beq_SymExpr e1 e2
      | Imm v1, Imm v2 => beq_val v1 v2
      | InitialReg l1, InitialReg l2 => beq_preg l1 l2
      | InitialMem l1, InitialMem l2 => beq_SymExpr l1 l2
      | Load addr1 as1 es1, Load addr2 as2 es2 =>
        leq_SE as1 as2 && leq_SE es1 es2 && beq_SymExpr addr1 addr2
      | _,_ => false
    end.

Fixpoint beq_MemState (a b :  list (Addr*SymExpr)) : bool :=
  match a, b with
    | nil, nil => true
    | (a1,s1)::xs, (a2,s2)::ys => beq_SymExpr a1 a2 && beq_SymExpr s1 s2 && beq_MemState xs ys
    | _,_ => false
  end.

Definition beq_constraint (a b : Constraint) : bool :=
  match a, b with
    | ReadMem a1, ReadMem a2 => beq_SymExpr a1 a2
    | WriteMem a1, WriteMem a2 => beq_SymExpr a1 a2
    | DivBy e1, DivBy e2 => beq_SymExpr e1 e2
    | _, _ => false
  end.

(* the type of our register store *)
Definition regs := @LocStore preg SymExpr beq_preg.

(* the type of our memory store *)
Definition mems := @LocStore SymExpr SymExpr beq_SymExpr.

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

Definition symSetMem (l : SymExpr) (x : SymExpr) (s : SymState) : SymState :=
  match s with
  | SymSt c m r => SymSt c (update l x m) r
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
Definition readMem (l : SymExpr) (s : SymState) : SymState :=
  match s with
    | SymSt c mapping r => SymSt (ReadMem l::c) mapping r
  end.

Definition writeMem (l : SymExpr) (s : SymState) : SymState :=
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
Definition initMem : mems := initLocStore beq_SymExpr (InitialMem).
Definition initReg : regs := initLocStore beq_preg (InitialReg).
Definition initSymSt : SymState := SymSt nil initMem initReg.

Notation "a # b" :=
  match b with
  | Register p  => (lookup p (symReg a))
  | Memory cnk =>
    let (addrs,syms) := split (store (symMem a)) in 
        Load cnk addrs syms  (* (lookup m (symMem a)) *)
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
                    else (mult (l # (Register r) ) (Imm (Vint sc)))
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
Definition single_symExec' (i : instruction) (l : SymState) : option SymState :=
  match i with
  | Pnop => Some l
      (** Moves *)
  | Pmov_rr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1))) (* (lookup (IR r1) (symReg l)))  (* (l # (Register r1))) *) *)
  | Pmov_ri rd n =>
      Some (l # (Register rd) <- (Imm (Vint n)))
  | Pmov_rm rd a =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (readMem aE (l # (Register rd) <- (l # (Memory aE))))
    end
  | Pmov_mr a r1 =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (writeMem aE (l # (Memory aE) <- (l # (Register r1))))
    end
  | Pmovd_fr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovd_rf rd r1 => 
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_ff rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_fi rd n =>
      Some (l # (Register rd) <- (Imm (Vfloat n))) 
  | Pmovsd_fm rd a =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (readMem aE (l # (Register rd) <- (l # (Memory aE))))
    end
  | Pmovsd_mf a r1 =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (writeMem aE (l # (Memory aE) <- (l # (Register r1))))
    end
  | Pfld_f r1 =>
      Some (l # (Register ST0) <- (l # (Register r1)))  (* We don't track flags for the FPU *)
  | Pfld_m a =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (readMem aE (l # (Memory aE) <- (l # (Register ST0))))
    end
  | Pfstp_f rd =>
      Some (l # (Register rd) <- (l # (Register ST0)))
  | Pfstp_m a =>
    match eval_addrmode a l with
      | None    => None
      | Some aE => Some (writeMem aE (l # (Memory aE) <- (l # (Register ST0))))
    end
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

Definition single_symExec i l :=
  let pc := Register PC in
  match single_symExec' i l with
        | Some l' => Some (l' # pc <- (add (l # pc) (Imm (Vint (Int.repr 1)))))
        | None    => None
      end.

(* Big step symbolic execution *)
Fixpoint symExec (c : code) (l : SymState) : option SymState :=
  match c with
    | nil => Some l
    | i :: is => match (single_symExec i l) with
                   | Some l' => symExec is l'
                   | None => None
                 end
  end.

Definition isCR (c : preg) : bool :=
  match c with
    | (CR _) => true
    | _ => false
  end.

(* The normalization of binOps determines what instruction weakening /
  replacement is acceptable from the optimizer.  The semantic
  correctness of this routine is critical, but not proven. *)
Fixpoint normalizeSymOp (o : SymOp) (e1 e2 : SymExpr) : SymExpr := 
  let default := binOp o e1 e2 in
  match o,e1,e2 with
  | SymAnd,_,Imm (Vint  x) => if Int.eq x (Int.repr 0) then e1 else default
  | SymMult,_,Imm (Vint x)   =>
    if Int.eq x (Int.repr 1)
      then e1
      else if Int.eq x (Int.repr 2) then add e1 e1 else default
(*  | SymShiftL,_,(Imm (Vint x)) => SymMult e1 (power 2 x) (* FIXME power of? *) *)
  | SymSub,_,(Imm (Vint x))    => if Int.eq x (Int.repr 0) then e1 else default
  | SymXor,_,(Imm (Vint x))    => if Int.eq x (Int.repr 0) then e1 else default
  | _,_,_ => binOp o e1 e2
  end.

(* doesNoAlias returns true when it can prove two addresses do not
   alias each other.  Always returning false is safe but means we
   catch fewer optimization opportunities - "false" means we miss any
   case where we load an address 'X' that is not the most recently
   store and all stores between now and 'X' are provably not alias of
   'X'.  *)
Definition doesNotAlias (a1 a2 : SymExpr) := false.


(* In much of the below work there would be great benefit to being
   able to have mutually recursive functions.  For example,
   "nonaliasedLookup" should be able to call "normalize" when
   comparing to addresses for equality (to allow more optimizations).
   Unfortunately, nonaliasedLookup is itself part of normalize so
   without making it a local function to "normalize" this isn't
   possible.

   These situations are commented, as a form of lamentation / protest,
   with MRF (Mutual Recusion FIXME).  *)

(* Normalize a lookup by replacing the expression with the
   stored value, but ONLY IF it can be proven not to alias. *)
Fixpoint nonaliasedLookup (a : Addr) (addrs : list Addr) (syms : list SymExpr) : SymExpr :=
  match addrs,syms with
    | a1::moreA,s1::moreS =>
      if beq_SymExpr a1 a  (* MRF *)
        then s1
        else
          if doesNotAlias a1 a
            then nonaliasedLookup a moreA moreS
            else Load a addrs syms
    | _,_ => Load a addrs syms
  end.

Lemma length_filter_lt_length_cons : forall (A : Type) (f : A -> bool) (xs : list A) (x : A),
  lt (length (filter f xs)) (length (x :: xs)).
Proof.
  induction xs.
  auto. intros. replace (length (x :: a :: xs)) with (length (a :: x :: xs)) by auto.
  replace (length (a :: x :: xs)) with (Datatypes.S (length (x :: xs))) ; try (simpl ; omega).
  case_eq (f a) ; intros.
  replace (length (filter f (a :: xs))) with (Datatypes.S (length (filter f (xs)))).
  apply lt_n_S. apply IHxs. simpl. rewrite H. reflexivity.

  simpl.  rewrite H. apply lt_trans with (m := length (x::xs)).
  apply IHxs. simpl. omega.
Qed.

Function normalizeMem (zipped : list (Addr * SymExpr)) {measure length zipped}: (list (Addr * SymExpr)) := 
    match zipped with
      | (a1,s1)::more =>
        let filterOp x := if beq_SymExpr (fst x) a1 then false else true in
        (a1,s1) :: normalizeMem (filter filterOp more)  (* MRF, fst x, a1 *)
      | _ => nil
    end.
Proof.
  intros. apply length_filter_lt_length_cons.
Qed.

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
    | InitialReg l => InitialReg l
    | InitialMem l => InitialMem l
    | Load a addrs syms => let (addrs', syms') := split (normalizeMem (combine addrs syms))
      in nonaliasedLookup a addrs' syms
  end.

Definition normalizeConstraint (c : Constraint) : Constraint :=
  match c with
    | DivBy se => DivBy (normalize se)
    | ReadMem a => ReadMem (normalize a)
    | WriteMem a => WriteMem (normalize a)
  end.

(* Test if 'a' is a subset of 'b' (normalizing & comparing constraints) *)
Fixpoint subset (a b : list Constraint) : bool :=
  match a with
    | nil => true
    | (x::xs) => 
      let elemCheck := (fun z => beq_constraint (normalizeConstraint z) (normalizeConstraint x)) in
        existsb elemCheck b && subset xs b
  end.

(* For memory to be valid it must be syntaxtically equal after normalization *)
Definition validMem (c : SymState) (d : SymState) : bool := 
  let (c',d') := (normalizeMem (store (symMem c)), normalizeMem (store (symMem d))) in
    beq_MemState c' d'.

(* Registers are valid if every register, except the flag register, has
   the same symbolic value.  This task is broken down into integer and
   floating point registers. *)
Fixpoint validIRegs (c d : SymState) : bool :=
  let ir i := Register (IR i) in
    let check x := beq_SymExpr (normalize (c # (ir x))) (normalize (d # (ir x))) in
      check EAX && check EBX && check ECX && check EDX && check ESI &&
      check EDI && check EBP && check ESP.

Fixpoint validFRegs (c d : SymState) : bool :=
  let ir i := Register (FR i) in
    let check x := beq_SymExpr (normalize (c # (ir x))) (normalize (d # (ir x))) in
      check XMM0 && check XMM1 && check XMM2 && check XMM3 &&
      check XMM4 && check XMM5 && check XMM6 && check XMM7.

Fixpoint validRegs (c d : SymState) : bool :=
  let ir i := Register i in
    let check x := beq_SymExpr (normalize (c # (ir x))) (normalize (d # (ir x))) in
      check PC && check ST0 && check RA &&
      validIRegs c d &&
      validFRegs c d.

(* Flags are valid if they are the same or become "more defined" *)
Definition validFlag (f : Loc) (c : SymState) (d : SymState) : bool :=
  beq_SymExpr (c # f) symUndef || beq_SymExpr (c # f) (d # f).

Definition validFlags (c : SymState) (d : SymState) : bool :=
  validFlag (Register (CR ZF)) c d && 
  validFlag (Register (CR PF)) c d && 
  validFlag (Register (CR CF)) c d && 
  validFlag (Register (CR SOF)) c d.

(* All constraints in the optimized code must appear in the pre-optimized code *)
Definition validConstraints (c : SymState) (d : SymState) : bool :=
  subset (constraints c) (constraints d).

(* To symbolic executions match if the flags, registers, memory
   states, and constraints match after being normalized. *)
Definition sameSymbolicExecution (c : option SymState) (d : option SymState) : bool :=
  match c, d with
    | Some c', Some d' =>
          validFlags c' d' &&
          validRegs c' d' &&
          validMem c' d' && 
          validConstraints c' d'
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
Parameter peephole_failed : Asm.code -> Asm.code -> unit.

(** Peephole optimization operates on "executable blocks" - lists of
    assembly code.  If the validator succeeds then we succeed, if it
    failes we call a logging routine (currently getting optimized
    away!)  and return the old (known-good) assembly code. *)
Definition opt_window (c : Asm.code) :=
  let d := ml_optimize c
  in if peephole_validate c d
      then d
      else let _ := peephole_failed c d in c.

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

(* To obtain the blocks of code for optimization, we break the
   instruction list into symbolically executable chunks separated by
   singletons of unexecutable instructions. *)
Function sym_executable_block (c : Asm.code) {measure length c} : list Asm.code :=
  match c with
    | nil => nil
    | x :: xs => match (single_symExec x initSymSt) with
                   | None => (x :: nil) :: (sym_executable_block xs)
                   | Some _ => let opts := only_opt_instrs xs 
                     in (x :: opts) :: sym_executable_block (skipn (length opts) xs)
                 end
  end.
  intros. simpl.
  apply le_lt_n_Sm. apply skipn_le.
  auto.
Qed.

Definition concat (c : list Asm.code) : Asm.code := fold_left (fun a b => a ++ b) c nil.

Definition optimize (c : Asm.code) : Asm.code :=
  let parts := sym_executable_block c in concat (map opt_window parts).
    
Definition transf_function (f: Asm.code) : res Asm.code :=
  OK (optimize f).

Definition transf_fundef (f : Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition peephole_transf_program (p : Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.