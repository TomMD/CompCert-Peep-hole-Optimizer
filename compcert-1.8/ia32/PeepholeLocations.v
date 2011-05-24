Require Import Coqlib.

Set Implicit Arguments.
Section LocStore.
  Variables key val : Type.
  Variable key_eq : forall a b : key, {a = b} + {a <> b}.

Definition a_list := list (key * val).

Record LocStore : Type := mkLocStore 
  { store : a_list;
    default : val;
    dec := key_eq
  }.

Definition initLocStore (d : val) := mkLocStore nil d.

Fixpoint update' (k : key) (v : val) (l : a_list) : a_list := 
  match l with
    | nil => (k, v) :: nil
    | (k', v') :: ls => if key_eq k k'
      then (k, v) :: ls
      else update' k v ls
  end.

Definition update (k : key) (v : val) (s : LocStore) : LocStore :=
  mkLocStore (update' k v (store s)) (default s).

Fixpoint lookup' (k : key) (l : a_list) : option val :=
  match l with
    | nil => None
    | (k', v') :: ls => if key_eq k k'
      then Some v'
      else lookup' k ls
  end.

Definition lookup (k : key) (s : LocStore) : val :=
  match lookup' k (store s) with
    | None => default s
    | Some v => v
  end.

Fixpoint elements' (l : a_list) : list key :=
  match l with
    | nil => nil
    | (k, _) :: ls => k :: elements' ls
  end.

Definition elements (s : LocStore) : list key :=
  elements' (store s).

End LocStore.




    