Require Import MachineInt.

Inductive Reg8 : Set := A : Reg8 | X : Reg8 | Y : Reg8.

Module AbstractRegister.

Module Context.

End Context.

Record RegF : Set :=
  mkState {
    RA: byte;
    RX: byte;
    RY: byte
}.

(*Inductive RegF : Set :=
 | mkState : byte -> byte -> byte -> RegF.*)


(*Inductive RegF (RA RX RY: byte) : Set :=
 | mkState : RegF RA RX RY.*)



Definition Inv_1 (B: RegF) : Prop := True.

(*Definition Inv_1 (RA RX RY: byte) : Prop := True.*)

Module Init.

Definition action : RegF := mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0).

Lemma PO_Safety: forall S: RegF, let S' := action in Inv_1 S.
intros S.
compute.
trivial.
Qed.

End Init.

Module SetRegister.

Definition setReg8 : RegF -> Reg8 -> byte -> RegF :=
  fun RF r b =>
    match r with
        A => mkState (b) (RF.(RX)) (RF.(RY))
      | X => mkState (RF.(RA)) (b) (RF.(RY))
      | Y => mkState (RF.(RA)) (RF.(RX)) (b)
    end.

Definition Guard : Prop := True.
Definition action (S : RegF) (r : Reg8) (b : byte) : RegF := setReg8 S r b.

Lemma PO_Safety: forall S: RegF, Guard -> let S' := action in Inv_1 S.
intros S.
simpl.
compute.
intro.
exact H.
Qed.

End SetRegister.

Module GetRegisterValue.

Definition getReg8 : RegF -> Reg8 -> byte :=
  fun RF r =>
    match r with
        A => RF.(RA)
      | X => RF.(RX)
      | Y => RF.(RY)
    end.

Definition Guard : Prop := True.
Definition action (S : RegF) (r : Reg8) : byte := getReg8 S r.

Lemma PO_Safety: forall S: RegF, Guard -> let S' := action in Inv_1 S.
intros S.
simpl.
compute.
intro.
exact H.
Qed.

End GetRegisterValue.

End AbstractRegister.