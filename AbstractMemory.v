Require Import MachineInt.
Require Import List.
Require Import Insert.

Module AbstractMemory.

Module Context.

Parameter nb_memories : nat.

End Context.

Definition Mem := list byte.

Definition Guard (l: nat) : Prop := l >= 0 /\ l < Context.nb_memories.

Module Init.
Definition Guard (limit:nat) : Prop := Context.nb_memories = limit.
End Init.

Module Store.

Definition Inv_1 (M: Mem) : Prop := True.

Definition store8 (M : Mem) (l : nat) (b : byte) : Mem := 
match replace_at M l b with 
| Some M' => M'
| None => M
end.

Definition action (S : Mem) (l : nat) (b : byte) : Mem := store8 S l b.

Lemma PO_Safety: forall S: Mem, forall l: nat, forall b: byte, Guard l -> let S' := action S l b in Inv_1 S'.
intros S l b.
simpl.
compute.
split.
Qed.

End Store.

Module Load.

Definition Inv_1 (b: byte) : Prop := True.

Definition load8 (M : Mem) (l : nat) : byte :=
    match skipn l M with
    | nil => Byte.repr 0
    | h :: t => h
    end.

Definition action (S : Mem) (l : nat) : byte := load8 S l.

Lemma PO_Safety: forall S: Mem, forall l: nat, Guard l -> let b' := action S l in Inv_1 b'.
intros S l.
compute.
split.
Qed.

End Load.


Lemma load_store_eq_8 :
  forall (M : Mem) (l : nat) (b : byte), Load.load8 (Store.store8 M l b) l = b.
intros S l b.
unfold Store.store8.
unfold replace_at.
compute.
simpl.
Admitted.


End AbstractMemory.
