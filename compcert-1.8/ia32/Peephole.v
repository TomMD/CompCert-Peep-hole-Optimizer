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

(* define equality for Loc, used in the Loc store *)
Lemma Loc_eq : forall (x y : Loc), {x = y} +  {x <> y}.
Proof.
  decide equality. 
  apply preg_eq.
  repeat decide equality; try apply Int.eq_dec.
Defined.

Inductive SymExpr : Type :=
  (* Integers *)
  | add    : SymExpr -> SymExpr -> SymExpr
  | sub    : SymExpr -> SymExpr -> SymExpr
  | mult   : SymExpr -> SymExpr -> SymExpr
  | div_unsigned : SymExpr -> SymExpr -> SymExpr
  | div_signed   : SymExpr -> SymExpr -> SymExpr
  | mod_unsigned : SymExpr -> SymExpr -> SymExpr
  | mod_signed   : SymExpr -> SymExpr -> SymExpr
  | shiftR : SymExpr -> SymExpr -> SymExpr
  | shiftR_unsigned : SymExpr -> SymExpr -> SymExpr
  | ror    : SymExpr -> SymExpr -> SymExpr
  | and    : SymExpr -> SymExpr -> SymExpr
  | or     : SymExpr -> SymExpr -> SymExpr
  | neg    : SymExpr -> SymExpr
  | xor    : SymExpr -> SymExpr -> SymExpr
  (* Tests *)
  | cmp    : SymExpr -> SymExpr -> SymExpr
  | test   : SymExpr -> SymExpr -> SymExpr  (* modifies x86 status register! *) 
  (* Floating *)
  | add_f  : SymExpr -> SymExpr -> SymExpr
  | sub_f  : SymExpr -> SymExpr -> SymExpr
  | mult_f : SymExpr -> SymExpr -> SymExpr
  | div_f  : SymExpr -> SymExpr -> SymExpr
  | abs_f  : SymExpr -> SymExpr
  | neg_f  : SymExpr -> SymExpr
  | Symbol : Loc -> SymExpr
  | Imm    : val -> SymExpr
  | Initial : Loc -> SymExpr.

(* here we use a map to store SymExpr in the symbolic execution. This
may not be the right choice because it's not immediately apparent how
to get everything back out of the map -- maybe we need to store a list
of Locs used as keys? *)

Module LocEq.
  Definition t := Loc.
  Definition eq := Loc_eq.
End LocEq.

Module Locmap := EMap(LocEq).

Definition locs := Locmap.t SymExpr.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Locmap.set b c a) (at level 1, b at next level).

Definition eval_addrmode (a: addrmode) (l : locs) : option SymExpr :=
  match a with Addrmode base ofs const =>
    match const with
      | inr (id, ofs') => None
      | inl ofs' => Some
        (add (match base with
               | None => (Imm Vzero)
               | Some r => (l (Register r))
             end)
        (add (match ofs with
                | None => (Imm Vzero)
                | Some(r, sc) =>
                  if Int.eq sc Int.one 
                    then (l (Register r)) 
                    else (mult (l (Register r)) (Imm (Vint sc)))
              end)
        (Imm (Vint ofs'))))
    end
  end.


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
      Some (l # (Memory a) <- (l (Register r1)))
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
      Some (l # (Register ST0) <- (l # (Register r1)))
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
      | Some v => Some (l # (Register rd) <- (add (l # (Register rd)) v))
      | None => None
    end
  | Pneg rd =>
      Some (l # (Register rd) <- (neg (l # (Register rd))))
  | Psub_rr rd r1 =>
      Some (l # (Register rd) <- (sub (l # (Register rd)) (l # (Register r1))))
  | Pimul_rr rd r1 =>
      Some (l # (Register rd) <- (mult (l # (Register rd)) (l # (Register r1))))
  | Pimul_ri rd n =>
      Some (l # (Register rd) <- (mult (l # (Register rd)) (Imm (Vint n))))
  | Pdiv r1 =>
      Some (l 
        # (Register EAX) <- 
          (div_unsigned (l # (Register EAX)) 
                        ((l # (Register EDX) <- (Imm Vundef)) (Register r1)))) 
        # (Register EDX) <- 
          (mod_unsigned (l # (Register EAX)) 
                        ((l #(Register EDX) <- (Imm Vundef)) (Register r1)))
  | Pidiv r1 =>
      Some (l 
        # (Register EAX) <- 
          (div_signed (l # (Register EAX)) 
                      ((l # (Register EDX) <- (Imm Vundef)) (Register r1)))) 
        # (Register EDX) <- 
          (mod_signed (l # (Register EAX)) 
                      ((l #(Register EDX) <- (Imm Vundef)) (Register r1)))
  | Pand_rr rd r1 =>
      Some (l # (Register rd) <- (and (l # (Register rd)) (l # (Register r1))))
  | Pand_ri rd n =>
      Some l # (Register rd) <- (and (l # (Register rd)) (Imm (Vint n)))
  | Por_rr rd r1 =>
      Some (l # (Register rd) <- (or (l # (Register rd)) (l # (Register r1))))
  | Por_ri rd n =>
      Some (l # (Register rd) <- (or (l # (Register rd)) (Imm (Vint n))))
  | Pxor_rr rd r1 =>
      Some (l # (Register rd) <- (xor (l # (Register rd)) (l # (Register r1))))
  | Pxor_ri rd n =>
      Some (l # (Register rd) <- (xor (l # (Register rd)) (Imm (Vint n))))
  | Psal_rcl rd =>
    (* FIXME!! not sure this is right, I know the 2^n is wrong *)
      match (l (Register ECX)) with
        | Imm (Vint n) => Some (l # (Register rd) <- (mult (l # (Register rd)) (Imm (Vint (Int.repr (2^(Int.intval n)))))))
        | _ => None
      end
  | Psal_ri rd n =>
      Some (l # (Register rd) <- (mult (l # (Register rd)) (Imm (Vint (Int.repr (2^(Int.intval n)))))))
  | Pshr_rcl rd =>
      Some (l # (Register rd) <- (shiftR (l # (Register rd)) (l # (Register ECX))))
  | Pshr_ri rd n =>
      Some (l # (Register rd) <- (shiftR_unsigned (l # (Register rd)) (Imm (Vint n))))
  | Psar_rcl rd =>
    (* probably not correct *)
          Some (l # (Register rd) <- (shiftR (l # (Register rd)) (l # (Register ECX))))
  | Psar_ri rd n =>
      Some (l # (Register rd) <- (shiftR (l # (Register rd)) (Imm (Vint n))))
  | Pror_ri rd n =>
      Some (l # (Register rd) <- (ror (l # (Register rd)) (Imm (Vint n))))
  | Pcmp_rr r1 r2 =>
      None (* Some ((compare_ints (rs r1) (rs r2) rs)) m*)
  | Pcmp_ri r1 n =>
      None (* Some ( (compare_ints (rs r1) (Vint n) rs)) m*)
  | Ptest_rr r1 r2 =>
      None (* Some ( (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs)) m *)
  | Ptest_ri r1 n =>
      None (* Some ( (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs)) m*)
  | Pcmov c rd r1 =>
     None (*
     (* FIXME!! needs rewrite of eval_testcond *)
      match eval_testcond c rs with
      | Some true => Some (l # (Register rd) <- (l (Register r1)))
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

Definition sameSymbolicExecution (c : option locs) (d : option locs) : bool. Admitted.

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

(** the initial state of our symbolic store returns the initial value
    for a given location. This means that no location is initially
    undefined and instead has the value "Initial foo" for the location
    "foo"*) 
Definition initLocs : locs := fun v => Initial v.

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

Lemma opt_window_size : forall c, Compare_dec.leb (length (opt_window c)) (length c) = true.
Proof.
  intros. unfold opt_window. unfold peephole_validate. destruct c. reflexivity.
  simpl.
Admitted.

Definition optWinSz : nat := 2%nat.

Function optimize (c : Asm.code) {measure length c} : Asm.code :=
  if Compare_dec.leb (length c) optWinSz
    then opt_window c
    else
      let o := opt_window (firstn optWinSz c) in
        let rec := skipn 1 o ++ skipn optWinSz c in
          firstn 1 o ++ optimize rec.
intros. induction c. inversion teq.
destruct c. inversion teq. simpl.  remember (opt_window (a :: i :: nil)) as c0. 
induction c0.
simpl.  omega.  destruct c0. simpl. omega.
rewrite app_length. simpl.  

destruct c0. simpl. omega.

(* Need lemma here *)
Admitted.

Definition transf_function (f: Asm.code) : res Asm.code :=
  OK (optimize f).

Definition transf_fundef (f : Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition peephole_transf_program (p : Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.