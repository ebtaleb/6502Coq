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

(*
Lemma belong: forall A : Set, forall l1 l2 l3 : list A, forall e : A, forall n : nat,
app l2 l3 = l1
-> l2 = firstn n l1 -> l3 = skipn n l1
-> (length l2 = n /\ length l3 = (length l1 - n) /\ length l1 >= 0 /\  n < length l1) 
-> replace_at l1 n e = app l2 (e::l3).
intros A l1 l2 l3 e n.
simpl.
intros H1 H2 H3 H4.

induction l1 as [|x lx].
+simpl.
rewrite app_eq_nil in H1.
inversion H1.
*)

Definition Inv_1 (M: option Mem) : Prop := True.

Definition store8 (M : Mem) (l : nat) (b : byte) : option Mem := replace_at M l b.

Definition action (S : Mem) (l : nat) (b : byte) : option Mem := store8 S l b.

Lemma PO_Safety: forall S: Mem, forall l: nat, forall b: byte, Init.Guard 4096 -> Guard l -> let S' := action S l b in Inv_1 S'.
intros S l b.
simpl.
compute.
intro.
rewrite H.
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

Lemma PO_Safety: forall S: Mem, forall l: nat, Init.Guard 4096 -> Guard l -> let b' := action S l in Inv_1 b'.
intros S l.
compute.
intro H.
rewrite H.
split.
Qed.

End Load.

(*
Lemma load_store_eq_8 :
  forall (M : Mem) (l : nat) (b : byte), Load.load8 (Store.store8 M l b) l = b.
intros S l b.
unfold Store.store8.
unfold Store.replace_at.
compute.
simpl.
*)

End AbstractMemory.
