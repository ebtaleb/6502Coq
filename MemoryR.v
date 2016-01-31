Require Import MachineInt.
Require Import AbstractMemory.
Require Import List.
Require Import Insert.

(** Raffinement de la mémoire qui prévient les accès à la mémoire non initialisée. *)

Module MemoryR.

Inductive outcome: Type :=
  | Safe: byte -> outcome
  | OutOfBoundsError : outcome
  | NonInitMemError: outcome.

Module Context.
Definition nb_memories : nat := AbstractMemory.Context.nb_memories.
End Context.

  Definition Mem := list byte.

  Definition Glue (st: Mem) (abs_st:AbstractMemory.Mem): Prop :=  True.
  (*Definition Glue (st: Mem) (abs_st:AbstractMemory.Mem): Prop :=  st = abs_st.*)

  Definition Inv1 (st:Mem) : Prop := True.

  Module Load.

Definition load8 (M : Mem) (l : nat) : outcome :=
    match nth' M l with
    | None => OutOfBoundsError
    | Some h => match Byte.isNI h with
                  | true => NonInitMemError
                  | false => Safe (Byte.repr (Byte.intval h))
                  end
    end.

Definition action (S : Mem) (l : nat) : outcome := load8 S l.

    Theorem PO_Safety_1 : forall (st:Mem) (abs_st:AbstractMemory.Mem), True.
    Proof.
    trivial.
    Qed.

  End Load.

Module Store.

Definition Guard (st: Mem) := True.

Definition store8 (M : Mem) (l : nat) (b : byte) : option Mem := insert' M l (Byte.reprInit (Byte.intval b)).

Definition action (S : Mem) (l : nat) (b : byte) : option Mem := store8 S l b.

Theorem PO_Simul : forall ( B : Mem ), 
forall ( AB : AbstractMemory.Mem ), forall (a : nat), forall (b : byte),
AbstractMemory.Inv_1 AB
-> Glue B AB
-> Inv1 B
-> Guard B
-> let B' := match action B a b with | Some (x) => x | _ => B end
in let AB' := AbstractMemory.Store.action AB a b
in Glue B' AB'.
    Proof.
    intros.
    unfold Glue.
    simpl.
    trivial.
    Qed.

End Store.

End MemoryR.