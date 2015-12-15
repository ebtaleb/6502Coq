Require Import Map.
Require Import Coqlib.
Require Import MachineInt.
Require Import M6502_Reg. 

Definition Label := Z.

Definition Mem := Map Label byte.

Definition emp : Mem := fun f => (None: option byte).

Axiom Mem_eq : forall M M' : Mem, (forall f, M f = M' f) -> M = M'.

Definition store8 (M : Mem) : Label -> byte -> Mem := put zeq M .

Definition load8 (M : Mem) (l : Label) : option byte := M l.

Lemma load_store_eq_8 :
  forall (M : Mem) (l : Label) (b : byte), load8 (store8 M l b) l = Some b.
Proof.
intros.
unfold load8.
unfold store8.
apply put_get_eq.
Qed.

Lemma store8_eq : 
  forall M l b, store8 M l b l = Some b.
Proof.
intros.
unfold store8.
apply put_get_eq.
Qed.

Lemma store8_neq :
  forall M l l' b, l <> l' -> M l' = store8 M l b l'.
intros.
unfold store8.
unfold put.
case (zeq l' l).
-intros.
 symmetry in e.
 contradiction.
-intros; trivial.
Qed.

Lemma load_store_neq_8 : 
  forall M x f b, x <> f -> load8 (store8 M x b) f = load8 M f.
  intros.
  unfold load8.
  symmetry.
  apply store8_neq.
  exact H.
Qed.

Fixpoint ldList (M : Mem) (l : Label) (n : nat) {struct n} : option (list byte) :=
  match n with
    O => Some nil
  | S n' => match M l with
	      None => None
            | Some b => match (ldList M (l+1) n') with
			  None => None
			| Some l' => Some (b :: l')
			end
	    end
  end.

Fixpoint storeList (M : Mem) (l : Label) (bl : list byte) {struct bl} : Mem :=
  match bl with
    | nil => M
    | b :: bl' => store8 (storeList M (l+1) bl') l b
  end.

Definition singleList : Label -> list byte -> Mem := storeList emp.

