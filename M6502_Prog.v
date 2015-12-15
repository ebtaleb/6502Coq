Require Import MachineInt.
Require Import M6502_Reg.
Require Import M6502_Instr.
Require Import M6502_Mem.
Require Import M6502_Proc.
Require Import Coqlib.
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

Section Repeat.

  Variable A : byte.
  Fixpoint repeat (x : byte) (n: nat ) :=
    match n with
      | O => nil
      | S k => x::(repeat x k)
    end.

  Theorem repeat_length x n:
    length (repeat x n) = n.
  Proof.
    induction n as [| k Hrec]; simpl; rewrite ?Hrec; reflexivity.
  Qed.

  Theorem repeat_spec n x y:
    In y (repeat x n) -> y=x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

End Repeat.

Definition StartR : RegF := mkState (Byte.repr 0) (Byte.repr 0) (Byte.repr 0) (Byte.repr 0) (Byte.repr 0) (Word.repr 0).

Definition StartM : Mem := singleList 0 (repeat (Byte.repr 0) 64).

Definition StartP : State := (StartR, StartM).

Definition prog1 : list Instr :=
  (LDA_ir (Byte.repr 1)) ::
  (LDX_ir (Byte.repr 2)) ::
  (LDY_ir (Byte.repr 0)) ::
  nil.

Fixpoint find_instr (pos: Z) (code: list Instr) : option Instr :=
  match code with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

Fixpoint step (S1 : State) (p: list Instr) : option State :=
      match find_instr (Word.intval (_pc S1)) p with
        Some i => match exec_instr i S1 with
                    Next S2 => Some S2
                    |Stuck => None
                    end
        | None => None
        end.

Eval compute in step StartP prog1.

Inductive ste: Label -> list Instr -> State -> State -> Prop :=
  | exec_step_O: forall S1, forall p, ste 0 p S1 S1
  | exec_step_n:
      forall cpc p i S1 S2,
      Word.intval (_pc S1) = cpc ->
      find_instr (cpc) p = Some i ->
      exec_instr i S1 = Next S2 ->
      ste (Word.intval (_pc S2)) p S1 S2.

Eval apply in ste 0 prog1 StartP StartP.

Fixpoint run (S1 : State) (p: list Instr) (n : nat) : State :=
  match n with
  | 0%nat => S1
  | S n' => match step S1 p with
              | Some S2 => run S2 p n'
              | None => S1
              end
end.

(*Eval compute in run StartP prog1.*)

(*Definition Safe (S:State) : Prop := forall n, exists S', step n S S'.*)