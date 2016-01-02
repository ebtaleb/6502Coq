Require Import AbstractRegister.
Require Import AbstractMemory.
Require Import MachineInt.

Definition PC := word.

Inductive Flag : Set :=
  | C : Flag
  | Z : Flag
  | I : Flag
  | D : Flag
  | B : Flag
  | V : Flag
  | Si : Flag.

Record Status : Set :=
  mkState {
  CF : bool;
  ZF : bool;
  InF : bool;
  DF : bool;
  BF : bool;
  VF : bool;
  SF : bool
}.

Definition State := (AbstractRegister.RegF * AbstractMemory.Mem * PC * Status)%type.

Definition _R (S : State) :=
  match S with
    | (R, _, _, _) => R
  end.

Definition _M (S : State) :=
  match S with
    | (_, M, _, _) => M
  end.

Definition _PC (S : State) :=
  match S with
    | (_, _, pc, _) => pc
  end.

Definition _ST (S : State) :=
  match S with
    | (_, _, _, st) => st
  end.

Module AbstractMachine.

Module Context.

End Context.

Definition Inv_1 (B: State) : Prop := True.

Module Init.

Definition Guard : Prop := True.

(*Theorem PO_Safety: forall S: State,
Guard S -> let S' := action S in Inv_1 S.*)

End Init.

End AbstractMachine.