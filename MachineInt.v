Require Import Coqlib.

Module Type BitsM.

  Parameter sz : nat.
  Parameter szRange : sz = 8%nat \/ sz = 16%nat.

End BitsM.

Module FI(szM: BitsM).

  Definition wordsize := szM.sz.

  Definition sizeRange : wordsize = 8%nat \/ wordsize = 16%nat := szM.szRange.
  Hint Resolve sizeRange : ints.

  Definition modulus : Z := two_power_nat wordsize.
  Definition half_modulus : Z := modulus / 2.

Definition in_range (x: Z) :=
  match x ?= 0 with
  | Lt => False
  | _  =>
    match x ?= modulus with
    | Lt => True
    | _  => False
    end
  end.

Record int: Set := mkint { intval: Z; intrange: in_range intval; _NI : bool }.

Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  if zlt (unsigned n) half_modulus
  then unsigned n
  else unsigned n - modulus.

Lemma mod_in_range:
  forall x, in_range (Zmod x modulus).
Proof.
  intro.
  generalize (Z_mod_lt x modulus (two_power_nat_pos wordsize)).
  intros [A B].
  assert (C: x mod modulus >= 0). omega.
  red. red in C. red in B. 
  rewrite B. destruct (x mod modulus ?= 0); auto. 
Qed.

Definition repr (x: Z) : int := 
  mkint (Zmod x modulus) (mod_in_range x) (true).

Definition reprInit (x: Z) : int := 
  mkint (Zmod x modulus) (mod_in_range x) (false).

Definition isNI (x: int) : bool := x.(_NI).

Definition zero := repr 0.
Definition one  := repr 1.

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).

Require Import ZArith.BinInt.

Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: int): int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: int) : int := repr (Z.lxor (unsigned x) (unsigned y)).

End FI.

Module BYTE_SZ <: BitsM.

  Definition sz := 8%nat.

  Definition szRange : sz = 8%nat \/ sz = 16%nat.
  Proof.
    left.
    unfold sz. auto.
  Qed.

End BYTE_SZ.

Module WORD_SZ <: BitsM.

  Definition sz := 16%nat.

  Definition szRange : sz = 8%nat \/ sz = 16%nat.
  Proof.
    right.
    unfold sz. auto.
  Qed.

End WORD_SZ.


Module Byte := FI BYTE_SZ.
Module Word := FI WORD_SZ.

Definition byte := Byte.int.
Definition word := Word.int.
