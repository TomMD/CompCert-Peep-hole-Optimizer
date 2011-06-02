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

Definition update (k : key) (v : val) (s : LocStore) : LocStore :=
  mkLocStore ((k, v) :: (store s)) (default s).

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

End LocStore.

