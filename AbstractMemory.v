Require Import MachineInt.
Require Import List.
Require Import Repeat.

Module AbstractMemory.

Module Context.

End Context.

Definition Mem := list byte.

Definition Inv_1 (B: Mem) : Prop := True.

Module Store.

Fixpoint replace_at {A:Set} (l: list A) (n : nat) (elt : A) : list A :=
    match l, n with
    | nil, _ => elt::nil
    | h :: t, 0 => elt::t 
    | h :: t, S n' => h :: replace_at t n' elt
    end.

Definition store8 (M : Mem) (l : nat) (b : byte) : Mem := replace_at M l b.

Definition Guard : Prop := True.
Definition action (S : Mem) (l : nat) (b : byte) : Mem := store8 S l b.

Lemma PO_Safety: forall S: Mem, Guard -> let S' := action in Inv_1 S.
intros S.
simpl.
compute.
intro.
exact H.
Qed.

End Store.

Module Load.

Definition load8 (M : Mem) (l : nat) : option byte :=
    match skipn l M with
    | nil => None
    | h :: t => Some h
    end.

Definition Guard : Prop := True.
Definition action (S : Mem) (l : nat) : byte :=
    match load8 S l with
    | None => Byte.repr 0
    | Some b => b
    end.

Lemma PO_Safety: forall S: Mem, Guard -> let S' := action in Inv_1 S.
intros S.
simpl.
compute.
intro.
exact H.
Qed.

End Load.

End AbstractMemory.
