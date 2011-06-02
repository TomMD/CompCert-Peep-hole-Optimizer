Require Import Coqlib.

Set Implicit Arguments.
Section LocStore.
  Variables key val : Type.
  Variable key_eq : forall a b : key, {a = b} + {a <> b}.

Definition a_list := list (key * val).

Record LocStore : Type := mkLocStore 
  { store : a_list;
    default : key -> val;
    dec := key_eq
  }.

Definition initLocStore (d : key -> val) := mkLocStore nil d.

(* Fixpoint update' (k : key) (v : val) (l : a_list) : a_list :=  *)
(*   match l with *)
(*     | nil => (k, v) :: nil *)
(*     | (k', v') :: ls => if key_eq k k' *)
(*       then (k, v) :: ls *)
(*       else (k', v') :: update' k v ls *)
(*   end. *)

Definition update (k : key) (v : val) (s : LocStore) : LocStore :=
  mkLocStore ((k, v) :: (store s)) (default s).

(* Fixpoint lookup' (k : key) (l : a_list) : option val := *)
(*   match l with *)
(*     | nil => None *)
(*     | (k', v') :: ls => if key_eq k k' *)
(*       then Some v' *)
(*       else lookup' k ls *)
(*   end. *)

Fixpoint lookup' (k : key) (s : a_list) (d : key -> val): val :=
  match s with
    | nil => d k
    | (k',v) :: ss => if  key_eq k' k then v else lookup' k ss d
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

Definition key_eq_bool (k k' : key) : bool.
refine(fun k k' =>  if (key_eq k k') then true else false).
Defined.

Lemma key_eq__eq : forall k k',
  key_eq_bool k k' = true -> k = k'.
intros. 
unfold key_eq_bool in H.
destruct (key_eq k k'). auto. inversion H.
Qed.

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
destruct (key_eq k k). reflexivity.
elimtype False.
apply n. reflexivity.
Qed.


End LocStore.
