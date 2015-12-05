Require Import MachineInt.

(** This file defines the 6502 CPU registers. *)

Inductive Reg8 : Set := A : Reg8 | X : Reg8 | Y : Reg8 | STATUS : Reg8 | FLAGS : Reg8.
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

Definition RegFile8 := Reg8 -> byte.
Definition RegFile16 := Reg16 -> word.

(* Register State *)
Definition RegFile := (list RegFile8 * RegFile16)%type.

Record RegF : Set :=
  mkState {
    RA: byte;
    RX: byte;
    RY: byte;
    RSTATUS: byte;
    RFLAGS: byte;
    RPC: word
  }.

Definition setFlag (b: byte) (f: Flag): byte :=
  match f with
  | FlagCF => Byte.repr 1
  | FlagZF => Byte.repr 1
  | FlagIF => Byte.repr 1
  | FlagDF => Byte.repr 1
  | FlagBF => Byte.repr 1
  | FlagVF => Byte.repr 1
  | FlagSF => Byte.repr 1
  end.

Definition clearFlag (b: byte) (f: Flag): byte :=
  match f with
  | FlagCF => Byte.repr 0
  | FlagZF => Byte.repr 0
  | FlagIF => Byte.repr 0
  | FlagDF => Byte.repr 0
  | FlagBF => Byte.repr 0
  | FlagVF => Byte.repr 0
  | FlagSF => Byte.repr 0
  end.

Definition getFlag (b: byte) (f: Flag): bool :=
  match f with
  | FlagCF => false
  | FlagZF => false
  | FlagIF => false
  | FlagDF => false
  | FlagBF => false
  | FlagVF => false
  | FlagSF => false
  end.

(*Definition setReg8 : RegFile -> Reg8 -> byte -> RegFile :=
  fun R r b =>
    match r with
      _ =>
    end.

Definition getReg8 : RegFile -> Reg8 -> byte :=
  fun R r => _RF8 R r.*)

