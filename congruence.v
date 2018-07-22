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

Theorem divides_mult : forall a k m, divides m a -> divides m (a * k).
Proof.
  unfold divides.
  intros.
  destruct H as [q H0].
  exists (q * k).
  Search (_ * (_ * _)).
  rewrite Zmult_assoc.
  rewrite H0.
  reflexivity.
Qed.

Theorem divides_opp : forall a m, divides m a -> divides m (-a).
Proof.
  intros.
  apply (divides_mult _ (-1) m) in H.
  Search (_ * -_).
  Search (_ * -_).
  Search (-_).
  rewrite Z.opp_eq_mul_m1.
  exact H.
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
  rewrite Z.add_opp_diag_r.
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


Theorem congruent_mult : forall a b c d m, congruent a c m -> congruent b d m -> congruent (a * b) (c * d) m.
Proof.
  unfold congruent.
  intros.
  cut (c * d - a * b = (c - a) * b + (d - b) * c).
  - intros. rewrite H1.
    apply (divides_mult (c - a) b m) in H.
    apply (divides_mult (d - b) c m) in H0.
    apply (divides_add _ _ _ H H0).
  - Search ((_ - _) * _).
    rewrite Z.mul_sub_distr_r.
    rewrite Z.mul_sub_distr_r.
    Search (_ * _ = _ * _).
    rewrite (Z.mul_comm b c).
    rewrite <- (Z.add_opp_r (c * b) (a * b)).
    rewrite <- (Z.add_opp_r (d * c) (c * b)).
    rewrite Z.add_shuffle3.
    rewrite <- (Z.add_comm (- (a * b)) _).
    Search (_ + -_).
    rewrite <- Z.add_assoc.
    rewrite (Z.add_opp_diag_r (c * b)).
    rewrite <- Zplus_0_r_reverse.
    rewrite (Z.mul_comm d c).
    rewrite Z.add_opp_r.
    reflexivity.
Qed.


Compute Z.div_eucl 6 5.

Lemma congruent_k : forall n m, m > 0 -> exists k, congruent k n m /\ 0 <= k < m.
Proof.
  unfold congruent.
  unfold divides.
  intros.
  assert (m <> 0) as HMisNotZero.
  omega.
  Compute (-6 mod 7).
  exists (n mod m).
  split.
  exists (n / m).
  rewrite <- Zeq_plus_swap.
  symmetry.
  apply (Z_div_mod_eq_full _ _ HMisNotZero).
  Search (_ mod _).
  apply (Z_mod_lt _ _ H).
Qed.

Lemma even_or_odd: forall n, congruent n 0 2 \/ congruent n 1 2.
Proof.
  intros.
  assert (2 > 0) as HTwoGtZero. omega.
  apply (congruent_k n 2) in HTwoGtZero.
  destruct HTwoGtZero as [q HNCongruentToLt2].
  elim HNCongruentToLt2.
  intros.
  apply congruent_comm in H.
  inversion H0.
  apply Zle_lt_or_eq in H1.
  elim H1.
  intros.
  assert (q = 1) as HQisOne.
  omega.
  rewrite HQisOne in H.
  right. assumption.
  intros.
  rewrite <- H3 in H.
  left.  assumption.
Qed.

Lemma every_number_is_even_or_odd_modulus : forall x, x mod 2 = 0 \/ x mod 2 = 1.
  intros.
  assert (2 > 0).
  omega.
  apply (Z_mod_lt x 2) in H.
  destruct H.
  apply Zle_lt_or_eq in H.
  destruct H.
  assert (x mod 2 = 1).
  omega.
  right.  exact H1.
  symmetry in H.
  left.  exact H.
Qed.

Lemma every_number_is_even_or_odd : forall x, exists k, x = 2 * k \/ x = 2 * k + 1.
Proof.
  intros.
  intros.
  exists (x / 2).

  remember (x mod 2) as r.
  assert (r = 0 \/ r = 1).
  rewrite Heqr.
  apply every_number_is_even_or_odd_modulus.
  rewrite Heqr in H.
  rewrite (Zplus_0_r_reverse (2 * (x / 2))) at 1.
  assert (2 > 0). omega.
  destruct H.
  left.
  rewrite <- H.
  rewrite <- (Z_div_mod_eq _ 2).
  reflexivity.
  exact H0.
  right.
  rewrite <- H.
  rewrite <- (Z_div_mod_eq _ 2).
  reflexivity.
  exact H0.
Qed.

Lemma every_number_is_even_or_odd_congruent : forall x, congruent x 0 2 \/ congruent x 1 2.
Proof.
  intros.
  remember (every_number_is_even_or_odd x) as H.
  destruct H as [k H0].
  unfold congruent.
  unfold divides.
  destruct H0.
  left.
  exists (-k).
  symmetry.
  rewrite Z.sub_0_l.
  omega.
  right.
  exists (-k).
  omega.
Qed.

Lemma congruent_squared : forall x, congruent x (x * x) 2.
Proof.
  intros x.
  remember (every_number_is_even_or_odd_congruent x) as HXIsEvenOrOdd.
  elim HXIsEvenOrOdd.
  intros.
  unfold congruent in H.
  unfold congruent.

  destruct H as [q J].


  destruct HeqHXIsEvenOrOdd.
  elim
  unfold congruent.
  unfold divides.
  Search (_ * _ - _).
  Search (_ * 1).
  rewrite <- Z.add_opp_r.
  rewrite <- (Z.mul_1_r (-x)).
  Search (- _ * _).
  rewrite Z.mul_opp_comm.
  Search (_ * _ + _ * _).
  rewrite <- Z.mul_add_distr_l.
  rewrite Z.add_opp_r.
  assert (2 <> 0) as H2IsNot0.
  omega.
  remember (every_number_is_even_or_odd_modulus x) as Hx_is_even_or_odd.
  destruct HeqHx_is_even_or_odd.
  destruct Hx_is_even_or_odd as [HEven | HOdd].
  - apply (Zmod_divides _ _ H2IsNot0) in HEven.
    destruct HEven as [k].
    exists (2 * k * k - k).
    rewrite H.
    Search (_ * (_ - _)).
    rewrite Zmult_minus_distr_l.
    rewrite Zmult_minus_distr_l.
    Search (_ * 1).
    rewrite Z.mul_1_r.
    rewrite Z.mul_shuffle1.
    Search (_ * (_ * _)).
    rewrite <- (Zmult_assoc 2 k k).
    rewrite Zmult_assoc.
    reflexivity.
  - Search (_ + _ mod _).
    rewrite <- Z_div_mod_eq.
    cut (1 mod 2 = 1).
    intros.
    rewrite <- H in HOdd.
    Search (_ mod _ = 0).

    compute.
    reflexivity.

    rewrite
    apply (
  remember (every_number_is_even_or_odd_congruent x) as H.
  destruct H as [H0 | H1].

  unfold congruent in H0.
  Check divides_mult.
  destruct HeqH.
  apply (divides_mult _ x 2) in H0.

  unfold divides in H0.
  destruct H0 as [k J0].
  exists (2 * k  * k + k).
  Search (0 - _).
  rewrite Z.sub_0_l in J0.

  unfold congruent.
  unfold divides.
  intros.


Theorem poly_congruence_pg_28 : ~(exists x, x * x - 117 * x + 31 = 0).
Proof.
  intro H.
  destruct H as [x H1].
  remember (even_or_odd x) as x_is_even_or_odd.
  destruct x_is_even_or_odd.

  unfold congruent in c.

  Lemma
*)