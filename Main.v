Require Import MachineInt.
Require Import Coqlib.
Require Import Repeat.

Require Import Instructions.
Require Import AbstractRegister.
Require Import AbstractMachine.

Definition StartR := AbstractRegister.mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0).

Definition StartM := repeat (Byte.repr 0) 4096.

Definition StartPC := Word.repr 0.

Definition StartST := AbstractMachine.mkState false false false false false false false.

Definition StartP := (StartR, StartM, StartPC, StartST).

Definition prog1 : list Instr :=
  (LDA_ir (Byte.repr 1)) ::
  (LDX_ir (Byte.repr 4)) ::
  (LDY_ir (Byte.repr 0)) ::
  (STX_rm 3) ::
  (LDX_ir (Byte.repr 2)) ::
  (LDX_mr 3) ::
  (STX_rm 6) ::
  nil.

Eval compute in run StartP prog1 100.

Definition prog2 : list Instr :=
  (LDX_ir (Byte.repr 4)) ::
  (STX_rm 6) ::
  (LDX_mr 6) ::
  nil.

Eval compute in run StartP prog2 2.

Definition prog3 : list Instr :=
  (LDX_ir (Byte.repr 4)) ::
  (LDX_mr 6) ::
  (STX_rm 6) ::
  nil.

Eval compute in run StartP prog3 3.
