Require Import List Ensembles.

Section minimal_logic.


Theorem False_cannot_be_proven : ~False.
Proof.
    unfold not.
    intros H.
    case H.
Qed.

End minimal_logic.

Section test_sets.

(* A included in B and B included in C implies A included in C *)

Variable U : Set.

Variable A B C: Ensemble U.

Theorem In_Transitive: (Included U A B) /\ (Included U B C) -> (Included U A C).
Proof.
    intros both_included.
    intros x.
    destruct both_included as [a_in_b b_in_c].
    intros a_in_x.
    apply b_in_c.
    apply a_in_b.
    apply a_in_x.
Qed.

Theorem Intersection_Commutes : Included U (Intersection U A B) (Intersection U B A).
Proof.
    intro x.
    intro x_in_a_b.
    elim x_in_a_b.
    intros.
    split.
    assumption.
    assumption.
Qed.

(* (A ∩ B) ∩ C = A ∩ (B ∩ C) *)

Theorem Intersection_Assoc : Included U (Intersection U (Intersection U A B) C) (Intersection U A (Intersection U B C)).
Proof.
    intro x.
    intro x_in_a_b_then_c.
    elim x_in_a_b_then_c.
    intros x0 x0_in_a_intersect_b.
    split.
    elim x0_in_a_intersect_b.
    intros.
    assumption.
    split.
    elim x0_in_a_intersect_b.
    intros.
    assumption.
    assumption.
Qed.

