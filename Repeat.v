Require Import MachineInt.
Require Import List.

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