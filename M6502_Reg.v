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
  | CF : Flag
  | ZF : Flag
  | IntF : Flag
  | DF : Flag
  | BF : Flag
  | VF : Flag
  | SF : Flag.

(* Register State *)

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
  | _ => Byte.repr 1
  end.

Definition clearFlag (b: byte) (f: Flag): byte :=
  match f with
  | _ => Byte.repr 0
  end.

Definition getFlag (b: byte) (f: Flag): bool :=
  match f with
  | _ => false
  end.

Definition setReg8 : RegF -> Reg8 -> byte -> RegF :=
  fun RF r b =>
    match r with
        A => mkState (b) (RF.(RX)) (RF.(RY)) (RF.(RSTATUS)) (RF.(RFLAGS)) (RF.(RPC))
      | X => mkState (RF.(RA)) (b) (RF.(RY)) (RF.(RSTATUS)) (RF.(RFLAGS)) (RF.(RPC))
      | Y => mkState (RF.(RA)) (RF.(RX)) (b) (RF.(RSTATUS)) (RF.(RFLAGS)) (RF.(RPC))
      | STATUS => mkState (RF.(RA)) (RF.(RX)) (RF.(RY)) (b) (RF.(RFLAGS)) (RF.(RPC))
      | FLAGS => mkState (RF.(RA)) (RF.(RX)) (RF.(RY)) (RF.(RSTATUS)) (b) (RF.(RPC))
    end.

Definition getReg8 : RegF -> Reg8 -> byte :=
  fun RF r =>
    match r with
        A => RF.(RA)
      | X => RF.(RX)
      | Y => RF.(RY)
      | STATUS => RF.(RSTATUS)
      | FLAGS => RF.(RFLAGS)
    end.

Definition setReg16 : RegF -> Reg16 -> word -> RegF :=
  fun RF r w =>
    match r with
        PC => mkState (RF.(RA)) (RF.(RX)) (RF.(RY)) (RF.(RSTATUS)) (RF.(RFLAGS)) (w)
    end.

Definition getReg16 : RegF -> Reg16 -> word :=
  fun RF r =>
    match r with
        PC => RF.(RPC)
    end.

