Require Import Coqlib.

Set Implicit Arguments.
Section LocStore.
  Variables key val : Type.
  Variable beq_key : forall a b : key, bool. (* {a = b} + {a <> b}. *)
Definition a_list := list (key * val).

Record LocStore : Type := mkLocStore 
  { store : a_list;
    default : key -> val;
    dec := beq_key
  }.

Definition initLocStore (d : key -> val) := mkLocStore nil d.

Definition update (k : key) (v : val) (s : LocStore) : LocStore :=
  mkLocStore ((k, v) :: (store s)) (default s).

Fixpoint lookup' (k : key) (s : a_list) (d : key -> val): val :=
  match s with
    | nil => d k
    | (k',v) :: ss => if  beq_key k' k then v else lookup' k ss d
  end.

Definition lookup (k : key) (s : LocStore) : val :=
  lookup' k (store s) (default s).

Fixpoint elements' (l : a_list) : list key :=
  match l with
    | nil => nil
    | (k, _) :: ls => k :: elements' ls
  end.

Definition elements (s : LocStore) : list key :=
  elements' (store s).

(*
Lemma key_eq_bool_refl : forall k,
  key_eq_bool k k = true.
intro. simpl. unfold key_eq_bool. simpl.
destruct (key_eq k k). reflexivity.
elimtype False.
apply n. reflexivity.
Qed.


(* lemmas about things stored in this structure *)
Lemma update_same : forall k v s,
  lookup k (update k v s) = v.
intros. unfold update. unfold lookup. simpl.
case_eq (beq_key k k). reflexivity. intros. rewrite beq_key_refl in H. inversion H.
Qed.
*)

End LocStore.
