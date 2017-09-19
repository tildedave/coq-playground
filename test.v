Require Import List Ensembles.

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
