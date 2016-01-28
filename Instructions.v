Require Import Coqlib.
Require Import MachineInt.

Inductive Instr : Set := 
  (* LOAD *)
  | LDA_ir : byte -> Instr
  | LDX_ir : byte -> Instr
  | LDY_ir : byte -> Instr
  | LDA_mr : nat -> Instr
  | LDX_mr : nat -> Instr
  | LDY_mr : nat -> Instr
  (* STORE *)
  | STA_rm : nat -> Instr
  | STX_rm : nat -> Instr
  | STY_rm : nat -> Instr
  (* ARITHMETIC *)
  | ADC_mr : nat -> Instr
  | SBC_mr : nat -> Instr
  (* MISC *)
  | NOP : Instr
.

Module Instructions.

Module Context.

End Context.

End Instructions.