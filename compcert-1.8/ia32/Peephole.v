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
  | Initial : Loc -> SymExpr.

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

(* to decide equality of symbolic expressions, we need to decide equality of values *)
Definition val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}.
refine (fun v1 v2 => 
  match v1 as v1 return {v1 = v2} + {v1 <> v2} with
    | Vundef => match v2 with
                  | Vundef => Utils.in_left
                  | _ => Utils.in_right
                end
    | Vint n => match v2 with
                  | Vint n' => if Int.eq_dec n n' then Utils.in_left else Utils.in_right
                  | _ => Utils.in_right
                end
    | Vfloat n => match v2 with
                    | Vfloat n' => if Float.eq_dec n n' then Utils.in_left else Utils.in_right
                    | _ => Utils.in_right
                  end
    | Vptr b n => match v2 with 
                    | Vptr b' n' => if zeq b b' 
                      then if Int.eq_dec n n' then Utils.in_left else Utils.in_right
                      else Utils.in_right
                    | _ => Utils.in_right
                  end
  end); try (f_equal; auto); try discriminate;
         unfold not; intro prem; inversion prem; auto.
Defined.

(* define equality for Loc, used in the Loc store *)
Lemma Loc_eq : forall (x y : Loc), {x = y} +  {x <> y}.
Proof.
  decide equality. 
  apply preg_eq.
  repeat decide equality; try apply Int.eq_dec.
Defined.

(* decide equality for symbolic operators *)
Lemma SymOp_eq : forall (x y : SymOp), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined. 

(* decide equality for symbolic expressions. note this is *syntactic* equality *)
Definition SymExpr_dec : forall (a b : SymExpr), {a = b} + {a <> b}.
  refine (fix f (a b : SymExpr) : {a = b} + {a <> b} :=
    match a, b as _ return _ with
      | binOp _ _ _, _ => _
      | _,_ => _
    end); decide equality; try (apply val_eq_dec); try (apply Loc_eq) ; try (apply SymOp_eq).
Defined.

(* the type of our location store *)
Definition locs := @LocStore Loc SymExpr Loc_eq.

Notation "a # b" := (lookup b a) (at level 1, only parsing).
Notation "a # b <- c" := (update b c a) (at level 1, b at next level).

(** the initial state of our symbolic store returns the initial value
    for a given location. This means that no location is initially
    undefined and instead has the value "Initial foo" for the location
    "foo". Not sure why I have to restate the decision procedure, but
    there it is *)
Definition initLocs : locs := initLocStore Loc_eq Initial.

Definition eval_addrmode (a: addrmode) (l : locs) : option SymExpr :=
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

Definition setAllFlags (l : locs) (e : SymExpr) : locs :=
  l # (Register (CR ZF)) <- e
    # (Register (CR CF)) <- e
    # (Register (CR PF)) <- e
    # (Register (CR SOF)) <- e.

(* small step symbolic execution *)
Definition single_symExec (i : instruction) (l : locs) : option locs :=
  match i with
      (** Moves *)
  | Pmov_rr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmov_ri rd n =>
      Some (l # (Register rd) <- (Imm (Vint n)))
  | Pmov_rm rd a =>
      Some (l # (Register rd) <- (l # (Memory a)))
  | Pmov_mr a r1 =>
      Some (l # (Memory a) <- (l # (Register r1)))
  | Pmovd_fr rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovd_rf rd r1 => 
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_ff rd r1 =>
      Some (l # (Register rd) <- (l # (Register r1)))
  | Pmovsd_fi rd n =>
      Some (l # (Register rd) <- (Imm (Vfloat n))) 
  | Pmovsd_fm rd a =>
      Some (l # (Register rd) <- (l # (Memory a)))
  | Pmovsd_mf a r1 =>
      Some (l # (Memory a) <- (l # (Register r1)))
  | Pfld_f r1 =>
      Some (l # (Register ST0) <- (l # (Register r1)))  (* We don't track flags for the FPU *)
  | Pfld_m a =>
      Some (l # (Memory a) <- (l # (Register ST0)))
  | Pfstp_f rd =>
      Some (l # (Register rd) <- (l # (Register ST0)))
  | Pfstp_m a =>
      Some (l # (Memory a) <- (l # (Register ST0)))
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
      Some (setAllFlags (l 
        # (Register EAX) <- 
          (div_unsigned (l # (Register EAX)) 
                        ((l # (Register EDX) <- (Imm Vundef)) # (Register r1)))
        # (Register EDX) <- 
          (mod_unsigned (l # (Register EAX))
                        ((l # (Register EDX) <- (Imm Vundef)) # (Register r1)))) symUndef)
  | Pidiv r1 =>
      Some (setAllFlags (l 
        # (Register EAX) <- 
          (div_signed (l # (Register EAX)) 
                      ((l # (Register EDX) <- (Imm Vundef)) # (Register r1)))) 
        # (Register EDX) <- 
          (mod_signed (l # (Register EAX)) 
                      ((l # (Register EDX) <- (Imm Vundef)) # (Register r1))) symUndef)
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


Fixpoint symExec (c : code) (l : locs) : option locs :=
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


Fixpoint allLocs_dec (l : list Loc) (a b : locs) : bool :=
  match l with
    | nil => true
    | l' :: ls => 
      if SymExpr_dec (a # l') (b # l') 
        then allLocs_dec ls a b
        else false
  end.

Definition isCR (c : Loc) : bool :=
  match c with
    | (Register (CR _)) => true
    | _ => false
  end.

Fixpoint all {A : Type} (p : A -> bool) (xs : list A) : bool :=
  match filter (fun x => negb (p x)) xs with
    | nil => true
    | _   => false
  end.

Definition validFlags (x : list Loc) (c : locs) (d : locs) : bool := 
  all (fun l => SymExpr_dec (c # l) symUndef || SymExpr_dec (c # l) (d # l)) x.

Definition sameSymbolicExecution (c : option locs) (d : option locs) : bool :=
  match c, d with
    | Some c', Some d' =>
      let (flagC, nonFlagC) := partition (fun x => isCR x) (elements c') in
        let (flagD, nonFlagD) := partition (fun x => isCR x) (elements d') in
          allLocs_dec (nonFlagC ++ nonFlagD) c' d' && validFlags (flagC ++ flagD) c' d'
    | _, _ => false
  end.

(** peephole_validate validates the code optimized by the untrusted
  optimizer is semantically correct.  We only need to prove that
  peephole_validate returns true only when the two inputs are
  semantically correct.  It would be nice to have a proof that it
  doesn't return false given certain known-correct conditions, but
  that isn't required.
 *)
Fixpoint peephole_validate (c : Asm.code) (d : Asm.code) (l : locs) : bool :=
  if (negb (beq_nat (length c) 0)) && Compare_dec.leb (length d) (length c)
    then sameSymbolicExecution (symExec c l) (symExec d l)    
    else false.

Parameter ml_optimize : Asm.code -> Asm.code.

(** Peephole optimization of function level lists of assembly code. We
  feed the optimizer sliding windows of up to 4 instructions and then
  validate the results returned. If the results are valid, they are
  used, otherwise, they are discarded. **)
Definition opt_window (c : Asm.code) :=
  let c' := ml_optimize c
  in if peephole_validate c c' initLocs
      then c'
      else c.

Lemma opt_window_nil_nil : opt_window nil = nil.
  unfold opt_window. unfold peephole_validate. reflexivity.
Qed.

Lemma leb_n_n_true : forall n, true = Compare_dec.leb n n.
Proof.
  intros. induction n ; auto.
Qed.

Lemma opt_window_size : forall c, true = Compare_dec.leb (length (opt_window c)) (length c).
Proof.
  intros. unfold opt_window. unfold peephole_validate. destruct c. reflexivity.
  simpl. remember (Compare_dec.leb (length (ml_optimize (i :: c)))
                 (Datatypes.S (length c))) as len.
  destruct len. remember (sameSymbolicExecution
              match single_symExec i initLocs with
              | Some l' => symExec c l'
              | None => None
              end (symExec (ml_optimize (i :: c)) initLocs)) as ssE.
  destruct ssE. assumption. simpl. apply leb_n_n_true. simpl. apply leb_n_n_true.
Qed.

Fixpoint partitionSymExec (c : Asm.code) : (Asm.code * Asm.code) :=
  match c with
    | nil     => (pair nil nil)
    | (x::xs) => match single_symExec x initLocs with
                   | None => pair nil (x::xs)
                   | _    => let (cs,bs) := partitionSymExec xs in pair (x::cs) bs
                     end
    end.

Fixpoint optimize (c : Asm.code) {measure length c} : Asm.code :=
  let part := partitionSymExec c in
    let len := length (fst part) in
      match snd part with
        | nil     => opt_window (fst part)
        | (r::rs) => opt_window (fst part) ++ (r::skipn (len + 1) c)
    end.

Definition transf_function (f: Asm.code) : res Asm.code :=
  OK (optimize f).

Definition transf_fundef (f : Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition peephole_transf_program (p : Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.