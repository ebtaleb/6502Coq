Require Import M6502_Reg.
Require Import M6502_Mem.

Definition State := (RegF * Mem)%type.

Definition _R (S : State) :=
  match S with
    | (R, _) => R
  end.

Definition _M (S : State) :=
  match S with
    | (_, M) => M
  end.

Definition _pc :=
  (fun S : State => getReg16 (_R S) PC).
