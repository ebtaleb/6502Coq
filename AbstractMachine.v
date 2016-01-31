Require Import Coqlib.
Require Import MachineInt.
Require Import Repeat.

Require Import AbstractRegister.
Require Import AbstractMemory.
Require Import MemoryR.
Require Import Instructions.

(**
- C	....	Retenue (Carry) ) posé si le complément à deux du résultat après une instruction ADC ou SBC est inférieur à -128 ou supérieur à 127
- Z	....	Zero
- I	....	Interruptions non autorisées si le drapeau est posé
- D	....	Mode décimal codé binaire
- B	....	Break
- V	....	Débordement (Overflow)
- N	....	Nombre négatif (Signe)
*)

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

(** 
L'état d'une machine se compose :
- des registres de calcul A (accumulateur), X et Y sur 8 bits,
- d'une mémoire avec un bus d'adresse sur 16 bits,
- d'un compteur ordinal sur 16 bits,
- et d'un registre de status contenant les différents drapeaux.
*)

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

(**
Si l'instruction a été exécutée correctement, le constructeur Next contient
le nouvel état de la machine.
Sinon, la machine se trouve bloquée.
*)

Inductive outcome: Type :=
  | Next: State -> outcome
  | Stuck: outcome.

(** On définit ici les fonctions implémentant le comportement des instructions. 
*)

Definition exec_jmp_abs (S: State) (w: word) :=
Next (R S, M S, w, ST S).

Definition exec_jmp_indirect (S: State) (a:nat) :=
  match MemoryR.Load.load8 (M S) (a+1) with
  | MemoryR.Safe v1 =>   match MemoryR.Load.load8 (M S) (a+2) with
                        | MemoryR.Safe v2 => Next (R S, M S, (Word.repr (Byte.intval (Byte.or v1 v2))), ST S)
                        | _ => Stuck
                        end
  | _ => Stuck
  end.

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

Definition exec_adc_mr (a: nat) (S : State) :=
  match MemoryR.Load.load8 (M S) a with
  | MemoryR.Safe v => let res := Byte.add (v) (AbstractRegister.GetRegisterValue.getReg8 (R S) A) in
                      Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A res, M S, PC S, ST S))
  | _ => Stuck
  end.

Definition exec_adc_imm (b: byte) (S : State) :=
    let res := Byte.add (b) (AbstractRegister.GetRegisterValue.getReg8 (R S) A) in match (ST S).(CF) with
    | true => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A (Byte.add res Byte.one), M S, PC S, ST S))
    | false => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A res, M S, PC S, ST S))
    end.

Definition exec_sbc_mr (a: nat) (S : State) :=
  match MemoryR.Load.load8 (M S) a with
  | MemoryR.Safe v => let res := Byte.sub (AbstractRegister.GetRegisterValue.getReg8 (R S) A) (v) in
                      Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A res, M S, PC S, ST S))
  | _ => Stuck
  end.

Definition exec_sbc_imm (b: byte) (S : State) :=
    let res := Byte.sub (AbstractRegister.GetRegisterValue.getReg8 (R S) A) (b) in match (ST S).(CF) with
    | true => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A (Byte.sub res Byte.one), M S, PC S, ST S))
    | false => Next (nextinstr (AbstractRegister.SetRegister.setReg8 (R S) A res, M S, PC S, ST S))
    end.

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
  | ADC_ir b => exec_adc_imm b S
  | SBC_ir b => exec_sbc_imm b S
  | ADC_mr l => exec_adc_mr l S
  | SBC_mr l => exec_sbc_mr l S
  | JMP_abs w => exec_jmp_abs S w
  | JMP_ind w => exec_jmp_indirect S w
  | _ => Next (S)
end.

(** Fonctions d'exécution des programmes. *)

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

(** Les états initiaux des différents éléments de la machine.
Bien sur, dans une machine réelle, ces états sont indéterminés et peuvent contenir
n'importe quoi.
*)

Definition StartR := AbstractRegister.mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0).

Definition StartM := repeat (Byte.repr 0) 4096.

Definition StartPC := Word.repr 0.

Definition StartST := mkState false false false false false false false.

Definition StartP := (StartR, StartM, StartPC, StartST).