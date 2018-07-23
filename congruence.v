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

Theorem divides_opp : forall a m, divides m a <-> divides m (-a).
Proof.
  split.
  intro H.
  apply (divides_mult _ (-1) m) in H.
  rewrite Z.opp_eq_mul_m1.
  exact H.
  intro H.
  apply (divides_mult _ (-1) m) in H.
  cut (- a * -1 = a).
  intros.
  rewrite H0 in H.
  exact H.
  ring.
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

Lemma congruent_k : forall n m, m > 0 -> exists k, congruent k n m /\ k = n mod m.
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
  reflexivity.
Qed.

Lemma congruent_0 : forall a b m, congruent a b m -> congruent (b - a) 0 m.
Proof.
  intros.
  unfold congruent.
  unfold congruent in H.
  apply divides_opp.
  replace (- (0 - (b - a))) with (b - a).
  assumption.
  ring.
Qed.

Lemma squeeze : forall a b m, b > 0 -> a < b -> a > -b -> a = m * b -> a = 0.
Proof.
  intros a b m HMGt0 H0 H1 HDivisible.
  assert (m = 0).
  rewrite HDivisible in H0, H1.
  Search (_ * _ <= _).
Admitted.

Theorem congruent_equiv_mod : forall a b m, m > 0 -> congruent a b m <-> a mod m = b mod m.
Proof.
  split.
  intros.
  assert (exists k1, congruent k1 a m /\ k1 = a mod m).
  apply (congruent_k a m).
  assumption.
  assert (exists k2, congruent k2 b m /\ k2 = b mod m).
  apply (congruent_k b m).
  assumption.
  destruct H1 as [j1 [J1 J1']].
  destruct H2 as [j2 [J2 J2']].
  unfold congruent in J1, J2.
  apply divides_opp in J1.
  apply (divides_add _ _ _ J1) in J2.
  replace (- (a - j1) + (b - j2)) with (b - a - (j2 - j1)) in J2.
  fold (congruent (j2 - j1) (b - a) m) in J2.
  apply congruent_0, congruent_comm in H0.
  apply congruent_comm in J2.
  apply (congruent_assoc  _ _ _ _ H0) in J2.
  unfold congruent in J2.
  rewrite Z.sub_0_r in J2.
  unfold divides in J2.
  assert (0 <= j1 < m).
  rewrite J1'.
  apply (Z_mod_lt _ _ H).
  assert (0 <= j2 < m).
  rewrite J2'.
  apply (Z_mod_lt _ _ H).
  assert (j2 - j1 < m). omega.
  assert (j2 - j1 > -m). omega.
  inversion J2.
  assert (j2 - j1 = 0).
  symmetry in H5.
  rewrite <- Z.mul_comm in H5.
  apply (squeeze (j2 - j1) m x H H3 H4 H5).
  Search (_ - _ = 0).
  rewrite <- J1', <- J2'.
  apply Zeq_minus in H6.
  rewrite Z.sub_0_r in H6.
  Search (_ - _ = 0).
  apply Zminus_eq in H6.
  symmetry in H6.
  exact H6.
  ring.
  intros.
  apply congruent_comm.
  unfold congruent.
  Search (_ -> _ - _ = 0).
  apply Zeq_minus in H0.
  Search (_ mod _ = _ mod _).
  assert ((a mod m - b mod m) mod m = 0 mod m).
  Search (_ mod _ = _ mod _).
  rewrite H0. reflexivity.
  rewrite <- Zminus_mod in H1.
  Search (0 mod _).
  rewrite Zmod_0_l in H1.
  Search (_ mod _ = 0 -> _).
  Search (_ mod _ = 0 -> _).
  apply (Z_div_exact_2 _ _ H) in H1.
  unfold divides.
  exists ((a - b) / m).
  symmetry.
  exact H1.
Qed.

Lemma even_or_odd: forall n, congruent n 0 2 \/ congruent n 1 2.
Proof.
  intros.
  assert (2 > 0) as HTwoGtZero. omega.
  (* this is dumb *)
  assert (2 > 0) as HTwoGtZero'. exact HTwoGtZero.
  apply (congruent_k n 2) in HTwoGtZero.
  destruct HTwoGtZero as [q HNCongruentToLt2].
  elim HNCongruentToLt2.
  intros.
  apply congruent_comm in H.
  apply (Z_mod_lt n 2) in HTwoGtZero'.
  rewrite <- H0 in HTwoGtZero'.
  elim HTwoGtZero'.
  intros.
  cut (q = 0 \/ q = 1).
  intros.
  case H3 as [HQIsZero | HQIsOne].
  - left. rewrite <- HQIsZero. exact H.
  - right. rewrite <- HQIsOne. exact H.
  - omega.
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
  - intros.
    unfold congruent in H.
    unfold congruent.

    Search (0 - _).
    rewrite Z.sub_0_l in H.
    apply divides_opp in H.
    assert (divides 2 (x * x)).
    apply (divides_mult x x 2) in H.
    exact H.
    apply divides_opp in H.
    apply (divides_add _ _ 2 H0 H).
  - intros.
    unfold congruent in H.
    unfold congruent.
    apply (divides_mult _ x 2) in H.
    cut ((1 - x) * x = - (x * x - x)).
    intro HSimpl.
    rewrite HSimpl in H.
    apply divides_opp in H.
    exact H.
    ring.
Qed.

Theorem poly_congruence_pg_28 : ~(exists x, x * x - 117 * x + 31 = 0).
Proof.
  intro H.
  assert (congruent (-117) 1 2) as H117IsOdd.
  unfold congruent.
  unfold divides.
  exists (59).
  ring.
  assert (congruent 31 1 2) as H31IsOdd.
  unfold congruent.
  unfold divides.
  exists (-15).
  ring.
  destruct H as [x H1].
  assert (congruent (x * x - 117 * x + 31) 0 2) as HCongruentEquation.
  rewrite H1.
  apply congruent_refl.
  assert (congruent 0 0 2) as HZeroIsEven.
  apply congruent_refl.
  remember (congruent_squared x) as HXIsCongruentToItsSquare.
  remember (even_or_odd x) as Hx_is_even_or_odd.
  destruct Hx_is_even_or_odd as [HEven | HOdd].
  assert (congruent (x * x) 0 2).
  apply (congruent_comm _ _ _).
  destruct HeqHx_is_even_or_odd.
  apply congruent_comm in HEven.
  apply (congruent_assoc _ _ _ _ HEven HXIsCongruentToItsSquare).

  assert (congruent (-117 * x) 0 2).
  apply (congruent_mult (-117) x 1 0 2 H117IsOdd HEven).
  apply (congruent_add _ _ _ _ 2 H) in H0.
  apply (congruent_add _ _ _ _ 2 H0) in H31IsOdd.
  rewrite Z.add_0_l in H31IsOdd.
  assert (x * x + -117 * x + 31  = x * x - 117 * x + 31) as HRewrite. ring.
  rewrite HRewrite in H31IsOdd.

  rewrite <- Z.mul_opp_comm in H31IsOdd.

  simpl in H31IsOdd.

  apply (congruent_mult
  congruent_squared in HEven.

  unfold congruent in c.

  Lemma
*)