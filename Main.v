(** Ce fichier contient une série de programmes dont le but est de vérifier 
le bon fonctionnement de l'émulateur. *)

Require Import Coqlib.
Require Import MachineInt.

Require Import AbstractRegister.
Require Import AbstractMachine.
Require Import Instructions.

Definition prog1 : list Instr :=
  (LDA_ir (Byte.repr 1)) ::
  (LDX_ir (Byte.repr 4)) ::
  (LDY_ir (Byte.repr 0)) ::
  (STX_rm 3) ::
  (LDX_ir (Byte.repr 2)) ::
  (LDX_mr 3) ::
  (STX_rm 6) ::
  nil.

Eval compute in run StartP prog1 (length prog1).

Definition prog2 : list Instr :=
  (LDX_ir (Byte.repr 4)) ::
  (STX_rm 6) ::
  (LDX_mr 6) ::
  nil.

Eval compute in run StartP prog2 (length prog2).

Definition prog2bis : list Instr :=
  (LDX_ir (Byte.repr 4)) ::
  (LDX_mr 6) ::
  (STX_rm 6) ::
  nil.

Eval compute in run StartP prog2bis (length prog2bis).

Definition prog3 : list Instr :=
  (LDX_ir (Byte.repr 1)) ::
  (STX_rm 0) ::
  (LDX_ir (Byte.repr 2)) ::
  (STX_rm 1) ::
  (LDX_ir (Byte.repr 3)) ::
  (STX_rm 2) ::
  (ADC_mr 0) ::
  (ADC_mr 1) ::
  (ADC_mr 2) ::
  nil.

Eval compute in run StartP prog3 (length prog3).

Definition prog4 : list Instr :=
  (LDX_ir (Byte.repr 1)) ::
  (STX_rm 0) ::
  (LDX_ir (Byte.repr 2)) ::
  (STX_rm 1) ::
  (LDX_ir (Byte.repr 3)) ::
  (STX_rm 2) ::
  (ADC_mr 0) ::
  (ADC_mr 1) ::
  (ADC_mr 2) ::
  (SBC_mr 0) ::
  (SBC_mr 1) ::
  (SBC_mr 2) ::
  (SBC_mr 2) ::
  nil.

Eval compute in run StartP prog4 (length prog4).
