Require Import Coqlib.
Require Import MachineInt.
Require Import M6502_Reg.
Require Import M6502_Mem.
Require Import M6502_Proc.

Require Import hex.

Section M6502_Instr.

(** Instruction Set *)

Inductive Instr : Set := 
  (* LOAD *)
  | LDA_ir : byte -> Reg8 -> Instr
  | LDX_ir : byte -> Reg8 -> Instr
  | LDY_ir : byte -> Reg8 -> Instr
  (* STORE *)
  | STA_rm : byte -> Reg8 -> Instr
  | STX_rm : byte -> Reg8 -> Instr
  | STY_rm : byte -> Reg8 -> Instr
  (* ARITHMETIC *)
  | ADC : Instr
  | SBC : Instr
  (* TRANSFER *)
  | TAX : Instr
  | TAY : Instr
  | TXA : Instr
  | TYA : Instr
  (* BITWISE OPERATION *)
  | AND : Instr
  | ORA : Instr
  | EOR : Instr
  | BIT : Instr
  | ROL : Instr
  | ROR : Instr
  (* BRANCHING *)
  | JMP : Instr
  (* INCREMENT/DECREMENT *)
  | INC : Instr
  | INX : Instr
  | INY : Instr
  | DEC : Instr
  | DEX : Instr
  | DEY : Instr
  (* CLEAR/SET FLAGS *)
  | CLC : Instr
  | CLD : Instr
  | CLI : Instr
  | CLV : Instr
  | SEC : Instr
  | SED : Instr
  | SEI : Instr
  (* MISC *)
  | NOP : Instr
.

End M6502_Instr.

