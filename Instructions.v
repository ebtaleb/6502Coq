Require Import Coqlib.
Require Import MachineInt.

(** Définitions des instructions. *)

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
  | ADC_ir : byte -> Instr
  | SBC_ir : byte -> Instr
  | ADC_mr : nat -> Instr
  | SBC_mr : nat -> Instr
  (* BRANCHING *)
  | BVC_i_rel : nat -> Instr
  | BVS_i_rel : nat -> Instr
  | BCC_i_rel : nat -> Instr
  | BCS_i_rel : nat -> Instr
  | BNE_i_rel : nat -> Instr
  | BEQ_i_rel : nat -> Instr
  | JMP_abs : word -> Instr
  | JMP_ind : nat -> Instr
  (* COMPARISION *)
  | CMP_i : byte -> Instr
  | CPX_i : byte -> Instr
  | CPY_i : byte -> Instr
  (* INCREMENT/DECREMENT *)
  | INC : Instr
  | INX : Instr
  | INY : Instr
  | DEC : Instr
  | DEX : Instr
  | DEY : Instr
  (* MISC *)
  | NOP : Instr.

Module Instructions.

Module Context.

End Context.

End Instructions.