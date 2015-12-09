Module AbstractMachineState6502.

Module Context.

Parameter size_max: nat.

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

End AbstractMachineState6502.