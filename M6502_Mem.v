Require Import Map.
Require Import Coqlib.
Require Import MachineInt.
Require Import M6502_Reg. 

Definition Label := Z.

Definition Mem := Map Label byte.

Axiom Mem_eq : forall M M' : Mem, (forall f, M f = M' f) -> M = M'.


Definition store8 (M : Mem) : Label -> byte -> Mem := put zeq M .

Definition load8 (M : Mem) (l : Label) : option byte := M l.