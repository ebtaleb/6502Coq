Module AbstractMemory6502.

Module Context.

Parameter mem: Type.

(** [empty] is the initial memory state. *)
Parameter empty: mem.

End Context.

Record Registers : Set := mkState {




}.

Record State : Set = mkState {


}.

Definition Inv_1 (B: State) : Prop := True.

Module Init.

Definition Guard : Prop := True.
Definition action : State := mkState .

Theorem PO_Safety: forall S: State,
Guard S -> let S' := action S in Inv_1 S.


End Init.

End AbstractMemory6502.