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

(* A ∩ B = B ∩ A *)

Theorem Intersection_Commutes : Same_set U (Intersection U A B) (Intersection U B A).
Proof.
    refine (conj _ _).
    intro x.
    intro x_in_a_b.
    elim x_in_a_b.
    intros.
    split.
    assumption.
    assumption.
    intro x.
    intro x_in_b_a.
    elim x_in_b_a.
    intros.
    split.
    assumption.
    assumption.
Qed.

(* (A ∩ B) ∩ C = A ∩ (B ∩ C) *)

Theorem Intersection_Assoc : Same_set U (Intersection U (Intersection U A B) C) (Intersection U A (Intersection U B C)).
Proof.
    refine (conj _ _).
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
    intro x.
    intro x_in_a_then_b_c.
    elim x_in_a_then_b_c.
    intros x0 x0_in_a x0_in_b_intersect_c.
    split.
    split.
    assumption.
    elim x0_in_b_intersect_c.
    intros.
    assumption.
    elim x0_in_b_intersect_c.
    intros.
    assumption.
Qed.

(* A ∪ B = B ∪ A *)

Theorem Union_Commutes : Same_set U (Union U A B) (Union U B A).
Proof.
    refine (conj _ _).
    intro x.
    intro x_in_a_b_union.
    case x_in_a_b_union.
    intros.
    apply Union_intror.
    assumption.
    intros.
    apply Union_introl.
    assumption.
    intro x.
    intro x_in_b_a_union.
    case x_in_b_a_union.
    intros.
    apply Union_intror.
    assumption.
    intros.
    apply Union_introl.
    assumption.
Qed.

(* (A ∪ B) ∪ C = A ∪ (B ∪ C) *)

Theorem Union_Assoc : Same_set U (Union U (Union U A B) C) (Union U A (Union U B C)).
Proof.
    refine (conj _ _).
    intro x.
    intro x_in_a_b_union.
    elim x_in_a_b_union.
    intros x0 x0_in_a_union_b.
    elim x0_in_a_union_b.
    intros x1 x1_in_a.
    apply Union_introl.
    exact x1_in_a.
    intros x1 x1_in_b.
    apply Union_intror.
    apply Union_introl.
    exact x1_in_b.
    intros x0 x0_in_c.
    apply Union_intror.
    apply Union_intror.
    exact x0_in_c.
    intro x.
    intro x_in_a_union_b_c.
    elim x_in_a_union_b_c.
    intros x0 x0_in_a.
    apply Union_introl.
    apply Union_introl.
    exact x0_in_a.
    intro x0.
    intro x0_in_b_union_c.
    elim x0_in_b_union_c.
    intros x1 x1_in_b.
    apply Union_introl.
    apply Union_intror.
    exact x1_in_b.
    intros x1 x1_in_c.
    apply Union_intror.
    exact x1_in_c.
Qed.
