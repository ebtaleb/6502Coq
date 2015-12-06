Require Import M6502_Reg.
Require Import M6502_Mem.

Definition State := (Mem * RegF)%type.

Definition _M (S : State) :=
  match S with
    | (M, _) => M
  end.

Definition _R (S : State) :=
  match S with
    | (_, R) => R
  end.

Definition _pc :=
  (fun S : State => getReg16 (_R S) PC).

Require Import ZArith.BinInt.

Example test : Z.to_nat (Z.lxor 32 3) = 35.
Proof.
compute.
reflexivity.
Qed.