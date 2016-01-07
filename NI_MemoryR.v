Require Import MachineInt.
Require Import AbstractMemory.

Module NI_MemoryR.

Module Context.
Definition nb_memories : nat := AbstractMemory.Context.nb_memories.
End Context.

  Definition NIMem := list NIbyte.

  Definition Glue (st: NIMem) (abs_st:AbstractMemory.Mem): Prop := True.

  Definition Inv1 (st:NIMem) : Prop := True.

  Module Load.

    Definition Guard (st: NIMem) := True.

    
    Definition action (st: NIMem) := st.

    (** *** Obligations de preuves 
       L'obligation de preuve d'un raffinement doit prendre en compte l'état
       du système concret et l'état du système abstrait pour énoncer la
       préservation de l'invariant de l'abstrait au concret.
     *)
    Theorem PO_Safety_1 : forall (st:NIMem) (abs_st:AbstractMemory.Mem), True.
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

    Theorem PO_Simul : forall (st:NIMem) (abs_st:AbstractMemory.Mem), True.
    Proof.
    trivial.
    Qed.

  End Load.

  Module Store.

  End Store.

End NI_MemoryR.