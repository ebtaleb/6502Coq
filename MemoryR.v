Require Import MachineInt.
Require Import AbstractMemory.
Require Import List.
Require Import Insert.

Module MemoryR.

Inductive outcome: Type :=
  | Safe: byte -> outcome
  | OutOfBoundsError : outcome
  | NonInitMemError: outcome.

Module Context.
Definition nb_memories : nat := AbstractMemory.Context.nb_memories.
End Context.

  Definition Mem := list byte.

  Definition Glue (st: Mem) (abs_st:AbstractMemory.Mem): Prop := True.

  Definition Inv1 (st:Mem) : Prop := True.

  Module Load.

    Definition Guard (st: Mem) := True.

Definition load8 (M : Mem) (l : nat) : outcome :=
    match skipn l M with
    | nil => OutOfBoundsError
    | h :: t => match Byte.isNI h with
                  | true => NonInitMemError
                  | false => Safe (Byte.repr (Byte.intval h))
                  end
    end.

Definition action (S : Mem) (l : nat) : outcome := load8 S l.

    (** *** Obligations de preuves 
       L'obligation de preuve d'un raffinement doit prendre en compte l'état
       du système concret et l'état du système abstrait pour énoncer la
       préservation de l'invariant de l'abstrait au concret.
     *)
    Theorem PO_Safety_1 : forall (st:Mem) (abs_st:AbstractMemory.Mem), True.
    Proof.
    trivial.
    Qed.

    (** *** Simulation La propriété de simulation doit énoncer que
        l'action préserve l'invariant de collage. 
     *)


    (*
forall lim : nat ,
Guard lim
→ let B := action lim in
let AB := AbstractMemory.action lim
Glue_1 B AB
    *)

(*
forall ( B : NIMem ), forall ( AB : AbstractMemory.Mem ),
AbstractMemory.Inv_1 AB
-> Glue_1 B AB
-> Inv_1 B
-> Guard B
-> let B' := action B
in let AB' := AbstractMemory.Load.action AB
in Glue_1 B' AB'.
*)

    Theorem PO_Simul : forall (st:Mem) (abs_st:AbstractMemory.Mem), True.
    Proof.
    trivial.
    Qed.

  End Load.

Module Store.

Definition store8 (M : Mem) (l : nat) (b : byte) : option Mem := replace_at M l (Byte.reprInit (Byte.intval b)).

Definition action (S : Mem) (l : nat) (b : byte) : option Mem := store8 S l b.

End Store.

End MemoryR.