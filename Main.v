Require Import AbstractMachine.
Require Import Instructions.
Require Import AbstractRegister.
Require Import AbstractMemory.
Require Import MachineInt.
Require Import Coqlib.
Require Import Repeat.

Definition nextinstr (S: State) : State :=
(_R S, _M S, (Word.repr (Word.intval (_PC S) + 1)), _ST S).

Inductive outcome: Type :=
  | Next: State -> outcome
  | Stuck: outcome.

Definition exec_load (a: nat) (dest: AbstractRegister.Reg8) (S: State) :=
  match AbstractMemory.Load.load8 (_M S) a with
  | Some v => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (_R S) dest v, _M S, _PC S, _ST S))
  | None => Stuck
  end.

Definition exec_store (a: nat) (S: State) (source: AbstractRegister.Reg8) :=
  match AbstractMemory.Store.store8 (_M S) a (AbstractRegister.GetRegisterValue.getReg8 (_R S) source) with
  | m' => Next (nextinstr (_R S, m', _PC S, _ST S))
  end.

Definition exec_load_imm (b: byte) (S : State) (R : AbstractRegister.Reg8) :=
 Next (nextinstr (AbstractRegister.SetRegister.setReg8 (_R S) R b, _M S, _PC S, _ST S)).

Definition exec_instr (i: Instr) (S: State) :=
  match i with
    LDA_ir b => exec_load_imm b S A
  | LDX_ir b => exec_load_imm b S X
  | LDY_ir b => exec_load_imm b S Y
  | LDA_mr l => exec_load l A S
  | LDX_mr l => exec_load l X S
  | LDY_mr l => exec_load l Y S
  | STA_rm l => exec_store l S A
  | STX_rm l => exec_store l S X
  | STY_rm l => exec_store l S Y
  | ADC_mr l => Next (S)
  | SBC_mr l => Next (S)
  | _ => Next (S)
end.

Definition StartR : AbstractRegister.RegF := AbstractRegister.mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0).

Definition StartM : AbstractMemory.Mem := repeat (Byte.repr 0) 64.

Definition StartPC : word := Word.repr 0.

Definition StartST : Status := AbstractMachine.mkState false false false false false false false.

Definition StartP : State := (StartR, StartM, StartPC, StartST).

Definition prog1 : list Instr :=
  (LDA_ir (Byte.repr 1)) ::
  (LDX_ir (Byte.repr 4)) ::
  (LDY_ir (Byte.repr 0)) ::
  (STX_rm 3) ::
  (LDX_ir (Byte.repr 2)) ::
  (LDX_mr 3) ::
  (STX_rm 6) ::
  nil.

Fixpoint find_instr (pos: Z) (code: list Instr) : option Instr :=
  match code with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

Fixpoint step (S1 : State) (p: list Instr) : option State :=
      match find_instr (Word.intval (_PC S1)) p with
        Some i => match exec_instr i S1 with
                    Next S2 => Some S2
                    |Stuck => None
                    end
        | None => None
        end.

Eval simpl in step StartP prog1.

Fixpoint run (S1 : State) (p: list Instr) (n : nat) : State :=
  match n with
  | 0%nat => S1
  | S n' => match step S1 p with
              | Some S2 => run S2 p n'
              | None => S1
              end
end.

Eval compute in run StartP prog1 (length prog1).