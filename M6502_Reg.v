(** This file defines the 6502 CPU registers. *)

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

  Record int: Set := mkint { intval: Z; intrange: in_range intval }.

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
  mkint (Zmod x modulus) (mod_in_range x).

Definition zero := repr 0.
Definition one  := repr 1.

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

Inductive Reg8 : Set := A : Reg8 | X : Reg8 | Y : Reg8 | S : Reg8 | FLAGS : Reg8.
Inductive Reg16 : Set := PC : Reg16.

(** C : carry,
      Z : zero, 
      I : interrupt,
      D : decimal mode status, 
      B : breakpoint,
      Bit 5: not used. Supposed to be logical 1 at all times,
      V : overflow,
      S : sign
*)
 
Inductive Flag : Set :=
  | FlagCF : Flag
  | FlagZF : Flag
  | FlagIF : Flag
  | FlagDF : Flag
  | FlagBF : Flag
  | FlagVF : Flag
  | FlagSF : Flag.

Definition RegFile8 := Reg8 -> word.
Definition RegFile16 := Reg16 -> word.

Definition RegFile := (list RegFile8 * RegFile16)%type.

Definition setFlag (w: word) (f : Flag) : word :=
  match f with
  | FlagCF => Word.repr 1
  | FlagZF => Word.repr 1
  | FlagIF => Word.repr 1
  | FlagDF => Word.repr 1
  | FlagBF => Word.repr 1
  | FlagVF => Word.repr 1
  | FlagSF => Word.repr 1
  end.

Definition clearFlag (w : word) (f : Flag) : word :=
  match f with
  | FlagCF => Word.repr 0
  | FlagZF => Word.repr 0
  | FlagIF => Word.repr 0
  | FlagDF => Word.repr 0
  | FlagBF => Word.repr 0
  | FlagVF => Word.repr 0
  | FlagSF => Word.repr 0
  end.

Definition getFlag (w:word) (f : Flag) : bool :=
  match f with
  | FlagCF => false
  | FlagZF => false
  | FlagIF => false
  | FlagDF => false
  | FlagBF => false
  | FlagVF => false
  | FlagSF => false
  end.

