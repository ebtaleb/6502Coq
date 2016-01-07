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

(*Definition setFlag (S: Status) (f: Flag): Status :=
  match f with
  | Si => mkState S.() S.() S.() S.() S.() S.() true
  | V => mkState S.() S.() S.() S.() S.() true S.()
  | B => mkState S.() S.() S.() S.() S.() S.() true
  | D => mkState S.() S.() S.() S.() S.() S.() true
  | I => mkState S.() S.() S.() S.() S.() S.() true
  | Z => mkState S.() S.() S.() S.() S.() S.() true
  | C => mkState S.() S.() S.() S.() S.() S.() true.
  end.*)

(*Definition clearFlag (S: Status) (f: Flag): Status :=
  match f with
  | Si => 
  | V => 
  | B => 
  | D => 
  | I => 
  | Z => 
  | C => 
  end.*)

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

End Init.

End AbstractMachine.