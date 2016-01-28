Require Import Instructions.
Require Import AbstractRegister.
Require Import AbstractMemory.
Require Import MemoryR.
Require Import MachineInt.
Require Import Coqlib.

Inductive Flag : Set :=
  | C : Flag
  | Zero : Flag
  | I : Flag
  | D : Flag
  | B : Flag
  | V : Flag
  | Si : Flag.

Record Status : Set :=
  mkState {
  CF : bool;
  ZF : bool;
  InF : bool;
  DF : bool;
  BF : bool;
  VF : bool;
  SF : bool
}.

Definition setFlag (S: Status) (f: Flag): Status :=
  match f with
  | Si => mkState S.(CF) S.(ZF) S.(InF) S.(DF) S.(BF) S.(VF) true
  | V => mkState S.(CF) S.(ZF) S.(InF) S.(DF) S.(BF) true S.(SF)
  | B => mkState S.(CF) S.(ZF) S.(InF) S.(DF) true S.(VF) S.(SF)
  | D => mkState S.(CF) S.(ZF) S.(InF) true S.(BF) S.(VF) S.(SF)
  | I => mkState S.(CF) S.(ZF) true S.(DF) S.(BF) S.(VF) S.(SF) 
  | Zero => mkState S.(CF) true S.(InF) S.(DF) S.(BF) S.(VF) S.(SF) 
  | C => mkState true S.(ZF) S.(InF) S.(DF) S.(BF) S.(VF) S.(SF)
  end.

Definition clearFlag (S: Status) (f: Flag): Status :=
  match f with
  | Si => mkState S.(CF) S.(ZF) S.(InF) S.(DF) S.(BF) S.(VF) false
  | V => mkState S.(CF) S.(ZF) S.(InF) S.(DF) S.(BF) false S.(SF)
  | B => mkState S.(CF) S.(ZF) S.(InF) S.(DF) false S.(VF) S.(SF)
  | D => mkState S.(CF) S.(ZF) S.(InF) false S.(BF) S.(VF) S.(SF)
  | I => mkState S.(CF) S.(ZF) false S.(DF) S.(BF) S.(VF) S.(SF) 
  | Zero => mkState S.(CF) false S.(InF) S.(DF) S.(BF) S.(VF) S.(SF) 
  | C => mkState false S.(ZF) S.(InF) S.(DF) S.(BF) S.(VF) S.(SF)
  end.

Definition State := (AbstractRegister.RegF * AbstractMemory.Mem * word * Status)%type.

Definition R (S : State) :=
  match S with
    | (r, _, _, _) => r
  end.

Definition M (S : State) :=
  match S with
    | (_, m, _, _) => m
  end.

Definition PC (S : State) :=
  match S with
    | (_, _, pc, _) => pc
  end.

Definition ST (S : State) :=
  match S with
    | (_, _, _, st) => st
  end.

Definition nextinstr (S: State) : State :=
(R S, M S, (Word.repr (Word.intval (PC S) + 1)), ST S).

Inductive outcome: Type :=
  | Next: State -> outcome
  | Stuck: outcome.

Definition exec_load (a: nat) (dest: AbstractRegister.Reg8) (S: State) :=
  match MemoryR.Load.load8 (M S) a with
  | MemoryR.Safe v => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) dest v, M S, PC S, ST S))
  | _ => Stuck
  end.

Definition exec_store (a: nat) (S: State) (source: AbstractRegister.Reg8) :=
  match MemoryR.Store.store8 (M S) a (AbstractRegister.GetRegisterValue.getReg8 (R S) source) with
  | Some m' => Next (nextinstr (R S, m', PC S, ST S))
  | None => Stuck
  end.

Definition exec_load_imm (b: byte) (S : State) (r : AbstractRegister.Reg8) :=
 Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) r b, M S, PC S, ST S)).

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

Fixpoint find_instr (pos: Z) (code: list Instr) : option Instr :=
  match code with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

Fixpoint step (S1 : State) (p: list Instr) : option State :=
      match find_instr (Word.intval (PC S1)) p with
        Some i => match exec_instr i S1 with
                    Next S2 => Some S2
                    |Stuck => None
                    end
        | None => None
        end.

Fixpoint run (S1 : State) (p: list Instr) (n : nat) : option State :=
  match n with
  | 0%nat => Some S1
  | S n' => match step S1 p with
              | Some S2 => run S2 p n'
              | None => None
              end
end.