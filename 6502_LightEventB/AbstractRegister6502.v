Require Import MachineInt.

Module AbstractRegister6502.

Module Context.

Parameter reg: byte.

End Context.

Inductive Reg8 : Set := A : Reg8 | X : Reg8 | Y : Reg8 | STATUS : Reg8 | FLAGS : Reg8.

Record RegF : Set := mkState {
    RA: byte;
    RX: byte;
    RY: byte;
    RSTATUS: byte;
    RFLAGS: byte }.

Definition Inv_1 (B: RegF) : Prop := True.

Module Init.

Definition Guard : Prop := True.
Definition action : RegF := mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0) (Byte.repr 0) (Byte.repr 0).

Lemma PO_Safety: forall S: RegF, Guard -> let S' := action in Inv_1 S.
intros S.
simpl.
compute.
intro.
exact H.
Qed.

End Init.

Module EventSetRegister.

Definition setReg8 : RegF -> Reg8 -> byte -> RegF :=
  fun RF r b =>
    match r with
        A => mkState (b) (RF.(RX)) (RF.(RY)) (RF.(RSTATUS)) (RF.(RFLAGS))
      | X => mkState (RF.(RA)) (b) (RF.(RY)) (RF.(RSTATUS)) (RF.(RFLAGS))
      | Y => mkState (RF.(RA)) (RF.(RX)) (b) (RF.(RSTATUS)) (RF.(RFLAGS))
      | STATUS => mkState (RF.(RA)) (RF.(RX)) (RF.(RY)) (b) (RF.(RFLAGS))
      | FLAGS => mkState (RF.(RA)) (RF.(RX)) (RF.(RY)) (RF.(RSTATUS)) (b)
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

End EventSetRegister.

Module EventGetRegisterValue.

Definition getReg8 : RegF -> Reg8 -> byte :=
  fun RF r =>
    match r with
        A => RF.(RA)
      | X => RF.(RX)
      | Y => RF.(RY)
      | STATUS => RF.(RSTATUS)
      | FLAGS => RF.(RFLAGS)
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

End EventGetRegisterValue.

End AbstractRegister6502.