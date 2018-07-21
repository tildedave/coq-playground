Require Import ZArith BinIntDef.

Local Open Scope Z_scope.

Definition divides k m := exists q,  k * q = m.

Theorem divides_a_a : forall a, divides a a.
  unfold divides.
  intros.
  exists 1.
  Search (_ * 1).
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

Theorem divides_a_0 : forall a, divides a 0.
Proof.
  unfold divides.
  intros.
  exists 0.
  Search (_ * 0).
  rewrite Z.mul_0_r.
  reflexivity.
Qed.

Theorem divides_minus_comm : forall a b m, divides m (a - b) -> divides m (b - a).
Proof.
  unfold divides at 1.
  intros.
  destruct H as [x H1].
  unfold divides.
  exists (- x).
  rewrite <- Z.mul_opp_comm.
  Search (- _ * _).
  rewrite Z.mul_opp_l.

  Search (_ + - _).
  rewrite <- Z.add_opp_r.
  rewrite Z.add_comm.
  Search (- (_ - _)).
  rewrite <- Z.opp_sub_distr.
  Search (- _ = - _).
  rewrite Z.opp_inj_wd.
  exact H1.
Qed.

Theorem divides_add : forall  a b m, divides m a -> divides m b -> divides m (a + b).
Proof.
  unfold divides.
  intros.
  destruct H as [k0 J1].
  destruct H0 as [k1 J2].
  exists (k0 + k1).
  Search (_ * (_ + _)).
  rewrite Z.mul_add_distr_l.
  rewrite J1.
  rewrite J2.
  reflexivity.
Qed.

Definition congruent a b m := divides m (b - a).

(* Chapter 3 proposition 3.2.1 *)

Theorem congruent_refl : forall a m, congruent a a m.
Proof.
  unfold congruent.
  intros.
  Search (_ - _).
  rewrite Zminus_diag.
  apply divides_a_0.
Qed.

Theorem congruent_comm : forall a b m, congruent a b m -> congruent b a m.
Proof.
  unfold congruent.
  intros.
  apply divides_minus_comm in H.
  exact H.
Qed.

Theorem congruent_assoc : forall a b c m, congruent a b m -> congruent b c m -> congruent a c m.
Proof.
  unfold congruent.
  intros.
  Search (_ + 0).
  cut (c - a = c - b + (b - a)).
  intros.
  rewrite H1.
  apply (divides_add (c - b) (b - a) m H0 H).

  rewrite <- (Z.add_opp_r b a).
  rewrite <- (Z.add_opp_r c b).
  rewrite (Z.add_comm b _).
  rewrite <- Z.add_shuffle2.
  rewrite <- Zplus_0_r_reverse.


  rewrite <- Zplus_assoc_reverse.
  rewrite (Zplus_assoc_reverse c _ _).
  rewrite Z.add_opp_diag_l.
  rewrite <- Zplus_0_r_reverse.
  rewrite Z.add_opp_r.
  reflexivity.
Qed.

Theorem congruent_1_8_7 : congruent 1 8 7.
Proof.
  unfold congruent.
  unfold divides.
  exists 1.
  auto with arith.
Qed.

Theorem congruent_add : forall a b c d m , congruent a c m -> congruent b d m -> congruent (a + b) (c + d) m.
Proof.
  unfold congruent.
  intros.
  cut (c + d - (a + b) = c - a + (d - b)).
  - intros. rewrite H1. apply (divides_add _ _ m H H0).
  - rewrite <- (Z.add_opp_r _ _).
    rewrite Z.opp_add_distr.
    rewrite Z.add_shuffle1.
    rewrite Z.add_opp_r.
    rewrite Z.add_opp_r.
    reflexivity.
Qed.
