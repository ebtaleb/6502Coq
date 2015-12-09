
Section Map.

Set Implicit Arguments.

Variables A B : Set.

Variable beq_A : forall (x y : A), {x = y} + {x <> y}.

Definition Map := A -> option B.
                                                                                
Definition emp : Map :=
  fun a : A => None.
                                                                                
Definition put : Map -> A -> B -> Map :=
  fun M a b =>
    fun x => if (beq_A x a) then (Some b) else M x.

Definition remove : Map -> A -> Map :=
  fun M a =>
    fun x => if (beq_A x a) then None else M x.

Definition maps_to : Map -> A -> B -> Prop :=
  fun M a b => M a = Some b.

Definition in_dom : A -> Map -> Prop :=
  fun a M => exists b : B, M a = Some b.

Definition not_in_dom : A -> Map -> Prop :=
  fun a M => M a = None.

Definition merge : Map -> Map -> Map :=
  fun M1 M2 =>
    fun x =>
      match M1 x with
	None => M2 x
      | _ => M1 x
      end.

Definition disjoint : Map -> Map -> Prop :=
  fun M1 M2 =>
    forall (x : A), not_in_dom x M1 \/ not_in_dom x M2.

Definition subseteq : Map -> Map -> Prop :=
  fun M1 M2 =>
    forall (x : A), in_dom x M1 -> M1 x = M2 x.

Lemma put_get_eq : 
  forall (M : Map) (x: A) (y : B), (put M x y) x = Some y.
Proof.
intros.
unfold put.
case (beq_A x x).
auto.
intro.
assert (x=x). auto. contradiction.
Qed.

Lemma pub_indepedent:
  forall (M : Map) (x x' : A) (y : B), x <> x' -> (put M x y) x' = M x'.
Proof.
intros M x x' y x_neq.
unfold put.
case (beq_A x' x).
intro. assert (x = x'). symmetry. auto. contradiction.
auto.
Qed.

End Map.
