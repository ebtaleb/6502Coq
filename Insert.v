Require Import Arith.
Require Import List.
Import ListNotations.

(** On définit ici des fonctions d'indexage et d'insertion dans la mémoire
qui tiennent compte de sa taille.
Ainsi, on empêche les accès en dehors du domaine autorisé. *)

Lemma zltz: 0 < 0 -> False.
Proof.
  intros. contradict H. apply Lt.lt_irrefl.
Qed.

Lemma nltz: forall n: nat, n < 0 -> False.
Proof.
  intros. contradict H. apply Lt.lt_n_0.
Qed.

Lemma predecessor_proof: forall {X: Type} (n: nat) (x: X) (xs: list X),
  S n < length (x::xs) -> n < length xs.
Proof.
  intros. simpl in H. apply Lt.lt_S_n. assumption.
Qed.

Fixpoint safe_nth {X: Type} (xs: list X) (n: nat): n < length xs -> X :=
  match xs, n with
  | [], _ => fun pf => match nltz n pf with end
  | x::_, 0 => fun _ => x
  | x::xs', S n' => fun pf => safe_nth xs' n' (predecessor_proof n' x xs' pf)
  end.

Fixpoint safe_insert {X: Type} (xs: list X) (n: nat) (elt: X): n < length xs -> list X :=
  match xs, n with
    | nil, _ => fun pf => elt::nil
    | h::t, 0 => fun _ => elt::t
    | h :: t, S n' => fun pf => h :: safe_insert t n' elt (predecessor_proof n' h t pf)
    end.

Definition insert' {A:Type} (l: list A) (n : nat) (elt : A)  :=
match lt_dec n (length l) with
  | left pf => Some (safe_insert l n elt pf)
  | right _ => None
  end.

Definition nth' {A:Type} (l: list A) (n : nat) :=
match lt_dec n (length l) with
  | left pf => Some (safe_nth l n pf)
  | right _ => None
  end.

Eval compute in insert' [1;2;3] 2 4.
Eval compute in nth' [1;2;3] 0.
