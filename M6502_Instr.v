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
  | LDA_ir : byte -> Instr
  | LDX_ir : byte -> Instr
  | LDY_ir : byte -> Instr
  | LDA_rm : Label -> Instr
  | LDX_rm : Label -> Instr
  | LDY_rm : Label -> Instr
  (* STORE *)
  | STA_rm : byte -> Label -> Instr
  | STX_rm : byte -> Label -> Instr
  | STY_rm : byte -> Label -> Instr
  (* ARITHMETIC *)
  | ADC : Label -> Instr
  | SBC : Label -> Instr
  (* TRANSFER *)
  | TAX : Instr
  | TAY : Instr
  | TXA : Instr
  | TYA : Instr
  (* BITWISE OPERATION *)
  | AND : Instr
  | ORA : Instr
  | EOR : Instr
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

Definition nextinstr (S: State) : State :=
(setReg16 (_R S) PC (Word.repr (Word.intval (_pc S) + 1)), _M S).

Inductive outcome: Type :=
  | Next: State -> outcome
  | Stuck: outcome.

Definition exec_load (a: Label) (dest: Reg8) (S: State) :=
  match load8 (_M S) a with
  | Some v => Next (nextinstr (setReg8 (_R S) dest v, _M S))
  | None => Stuck
  end.

Definition exec_store (a: Label) (S: State) (source: Reg8) :=
  match store8 (_M S) a (getReg8 (_R S) source) with
  | m' => Next (nextinstr (_R S, m'))
  end.

Definition exec_load_imm (b: byte) (S : State) (R : Reg8) :=
 Next (nextinstr (setReg8 (_R S) R b, _M S)).

Definition exec_instr (i: Instr) (S: State) :=
  match i with
    LDA_ir b => exec_load_imm b S A
  | LDX_ir b => exec_load_imm b S X
  | LDY_ir b => exec_load_imm b S Y
  | STA_rm b l => exec_store l S A
  | STX_rm b l => exec_store l S X
  | STY_rm b l => exec_store l S Y
  | _ => Next (S)
end.


End M6502_Instr.

