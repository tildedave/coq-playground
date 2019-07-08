Require Import Znumtheory Zdiv ZArith.
Local Open Scope Z_scope.

Lemma mod_4: forall a, a mod 4 = 0 \/ a mod 4 = 1 \/ a mod 4 = 2 \/ a mod 4 = 3.
Proof.
  intros a.
  assert (4 > 0) as H4_gt_0.
  omega.
  remember (Z_mod_lt a 4 H4_gt_0).
  omega.
Qed.

Lemma H0_lt_4: (0 < 4). omega. Qed.
Lemma H1_lt_4: (1 < 4). omega. Qed.
Lemma H4_not_0: (4 <> 0). omega. Qed.
Lemma H2_div_4: (2 | 4). apply (Zdivide_intro _ _ 2); omega. Qed.

(* currently not used *)
Lemma sq_mod_4: forall a, a * a mod 4 = 0 -> (2 | a).
Proof.
  intros a a_sq_mod_4.
  apply (Zmod_divide _ _ H4_not_0) in a_sq_mod_4.
  apply (Zdivide_trans 2 4 (a * a) H2_div_4) in a_sq_mod_4.
  apply (prime_mult 2 prime_2) in a_sq_mod_4; destruct a_sq_mod_4; auto.
Qed.

Lemma mod_0_not_prime: forall p a, 1 < a < p -> p mod a = 0 -> ~ prime p.
Proof.
  intros p a H1_lt_a p_mod_0.
  assert (a <> 0) as a_not_0 by omega.
  try apply (Zmod_divide _ _ a_not_0) in p_mod_0.
  intros p_prime.
  remember (prime_divisors p p_prime a p_mod_0); omega.
Qed.

Lemma mod_4_eq_2_not_prime: forall p, 2 < p -> p mod 4 = 2 -> ~ prime p.
Proof.
  intros p H1_lt_p.
  intros Hp_mod.
  apply (Zmod_divide_minus _ _ _ H0_lt_4) in Hp_mod.
  destruct Hp_mod as [d hp].
  rewrite Z.sub_move_r in hp.
  replace (d * 4 + 2) with ((d * 2 + 1) * 2) in hp; [auto | omega].
  cut (p mod 2 = (d * 2 + 1) * 2 mod 2); [auto | rewrite hp; reflexivity].
  intros Cut.
  rewrite Z_mod_mult in Cut.
  apply (mod_0_not_prime p 2); [omega | exact Cut].
Qed.

Lemma mod_2_4: 2 mod 4 = 2. compute; reflexivity. Qed.

(* p > 4 makes the proof easier.
   p = 3 can't be written as a sum of squares and p = 1 isn't prime. *)
Theorem p_sumofsquares_easy:
  forall p x y, prime p -> p > 4 -> p = x * x + y * y -> p mod 4 = 1.
Proof.
  intros p x y p_prime p_gt_4 p_sumofsquares.
  cut (p mod 4 = (x*x + y*y) mod 4).
  intros Cut.
  rewrite (Z.add_mod _ _ _ H4_not_0) in Cut.
  rewrite (Zmult_mod x), (Zmult_mod y) in Cut.
  assert (1 < 4 < p) as H1_lt_4_lt_p by omega.
  assert (2 < p) as H2_lt_p by omega.
  destruct (mod_4 x) as [Hx | [Hx | [Hx | Hx]]];
    destruct (mod_4 y) as [Hy | [Hy | [Hy | Hy]]];
    rewrite Hx, Hy in Cut;
    simpl in Cut;
    try rewrite Zmod_0_l in Cut;
    try do 2 rewrite (Zmod_1_l _ H1_lt_4) in Cut;
    try rewrite mod_2_4 in Cut;
    try exact Cut;
    try apply (mod_0_not_prime _ _ H1_lt_4_lt_p) in Cut;
    try apply (mod_4_eq_2_not_prime _ H2_lt_p) in Cut;
    try contradict p_prime; exact Cut.
  rewrite p_sumofsquares; reflexivity.
Qed.

Lemma p_reciprocity: forall p,
    prime p -> p mod 4 = 1 -> exists x y, (p | x * x + y * y) /\ Zgcd x y = 1.
Admitted.

Lemma p_descent: forall p x y, prime p -> (p | x * x + y * y) /\ Zgcd x y = 1 -> exists a b, p = a^2 + b^2 /\ Zgcd a b = 1.
Admitted.

Definition sum_of_squares (N : Z) := exists x y, (N = x * x + y * y /\ rel_prime x y).

Lemma factor_difference_of_squares : forall a b, a * a - b * b = (a + b) * (a - b).
Proof.
  intros; ring.
Qed.

Lemma q_div_lemma: forall N q a b x y,
    N = a * a + b * b -> rel_prime a b -> prime q -> (q | N) ->
    q = x * x + y * y -> rel_prime x y ->
    (q | ((x * b + a * y) * (x * b - a * y))).
Proof.
  intros N q a b x y H_n Hab_rel_prime Hq_prime Hq_divides_N H_q Hxy_rel_prime.
  assert (q | (x * x * N - a * a * q)) as H1.
  apply Z.divide_sub_r; apply Z.divide_mul_r; [assumption | apply Z.divide_reflexive].
  - rewrite H_n in H1.
    rewrite H_q in H1 at 2.
    repeat rewrite Z.mul_add_distr_l in H1.
    replace (x * x * (a * a)) with (a * a * (x * x)) in H1 by ring.
    rewrite Z.add_add_simpl_l_l in H1.
    replace (x * x * (b * b)) with ((x * b) * (x * b)) in H1 by ring.
    replace (a * a * (y * y)) with ((a * y) * (a * y)) in H1 by ring.
    rewrite factor_difference_of_squares in H1.
    exact H1.
Qed.

Definition descent_modulus a m :=
  let m' := a mod m in
  if Z_le_dec (2 * m') m then
    m'
  else
    (a mod m) - m.

Lemma descent_modulus_le_m_div_2 : forall a m,
    m > 0 -> Z.abs (descent_modulus a m) <= m / 2.
Proof.
  intros a m m_gt_1.
  unfold descent_modulus.
  assert (m > 0) as m_gt_0 by omega.
  remember (Z_mod_lt a _ m_gt_0) as m'_bound.
  destruct Heqm'_bound.
  remember (a mod m) as m'.
  destruct (Z_le_dec (2 * m') m).
  - assert (0 <= m') by omega.
    apply Z.abs_eq_iff in H.
    rewrite H.
    apply Zdiv_le_lower_bound; omega.
  - assert (a mod m - m <= 0) as HQuantityNegative by omega.
    rewrite <- Heqm' in HQuantityNegative.
    apply Z.abs_neq_iff in HQuantityNegative.
    rewrite HQuantityNegative.
    apply Zdiv_le_lower_bound; omega.
Qed.

Lemma mod_eq: forall a b c, c > 0 -> (a - b) mod c = 0 -> a mod c = b mod c.
Proof.
  intros a b c c_gt_0 a_minus_b_mod.
  rewrite Zminus_mod in a_minus_b_mod.

  apply (Zmod_divides _ c) in a_minus_b_mod.


  destruct a_minus_b_mod as [x def_x].


Lemma descent_modulus_equiv_a_mod_m : forall a m,
    m > 0 -> (descent_modulus a m) mod m = a mod m.
Proof.
  intros a m m_gt_0.
  unfold descent_modulus.
  destruct (Z_le_dec (2 * (a mod m)) m).
  - apply (Z_mod_lt a m) in m_gt_0.
    rewrite Zmod_mod; reflexivity.
  - apply mod_eq; [omega|].
    replace (a mod m - m - a) with ((a mod m - a) - m) by ring.
    rewrite Zminus_mod, Z_mod_same_full, Z.sub_0_r, Zminus_mod.
    repeat rewrite Zmod_mod.
    rewrite Z.sub_diag, Zmod_0_l.
    reflexivity.
Qed.

(* N = a^2 + b^2 = m * p, return (c^2 + d^2)k*p, k < m *)
Definition descent a b q :=
  let N := a * a + b * b in
  let m := N / q in
  if Z.eq_dec m 1 then
    (1, a, b)
  else
    let (u, v) := (descent_modulus a m, descent_modulus b m) in
    ((u * u + v * v) / m, (a * u + b * v)/m, (b * u - a * v)/m).

(* 3^2 + 2^2 = 13 *)
(* 5^2 + 1 = 2 * 13 *)

Compute (descent 5 1 13).
Compute (descent 12 1 29).
Compute (descent (-7) 3 29).
Compute (descent 442 1 953).
Compute (descent 69 2 953).
Compute (descent (-15) (-41) 953).

Lemma square_gt_0: forall n, n <> 0 -> n * n > 0.
Proof.
  intros n n_not_zero.
  destruct n;
    [contradict n_not_zero; reflexivity |
     auto |
     rewrite <- Pos2Z.opp_pos, Z.mul_opp_opp];
    rewrite <- Pos2Z.inj_mul; apply Zgt_pos_0.
Qed.

Lemma Zgt_ge_incl: forall n m: Z, m > n -> m >= n.
  intros n m n_lt_m.
  apply Z.gt_lt in n_lt_m.
  apply Z.lt_le_incl in n_lt_m.
  rewrite Z.ge_le_iff.
  assumption.
Qed.

Lemma square_ge_0: forall n, n * n >= 0.
Proof.
  intros n.
  destruct n;
    [omega |
     auto |
     rewrite <- Pos2Z.opp_pos, Z.mul_opp_opp];
    rewrite <- Pos2Z.inj_mul; apply Zgt_ge_incl; apply Zgt_pos_0.
Qed.

Lemma gt_0_means_not_0: forall n, n > 0 -> n <> 0.
Proof.
  intros n n_not_zero.
  contradict n_not_zero.
  omega.
Qed.

Lemma sum_of_squares_positive: forall a b N,
  (a > 0 \/ b > 0) ->
  N = (a * a + b * b) ->
  N > 0.
Proof.
  intros a b N a_or_b_gt_0 def_N.
  destruct a_or_b_gt_0.
  - remember (square_gt_0 a (gt_0_means_not_0 a H)).
    remember (square_ge_0 b).
    omega.
  - remember (square_gt_0 b (gt_0_means_not_0 b H)).
    remember (square_ge_0 a).
    omega.
Qed.

Lemma div_positive: forall a b, a > 0 -> b > 0 -> (a | b) -> b / a > 0.
Proof.
  intros a b a_gt_0 b_gt_0.
  Search (_ | _).
  intros a_div_b.
  destruct a_div_b as [x def_of_x].
  cut (x > 0). intro Cut.
  rewrite def_of_x, (Z_div_mult_full _ _ (gt_0_means_not_0 a a_gt_0)); assumption.
  rewrite def_of_x in b_gt_0.
  apply (Zmult_gt_reg_r x 0 a); auto.
Qed.

Lemma square_le_lemma: forall m, m > 0 -> (m / 2) * (m / 2) <=  (m * m) / 4.
Proof.
  intros m m_gt_0.
  replace 4 with (2 * 2) by auto.
  apply Zdiv_le_lower_bound; [omega | auto].
  replace ((m / 2) * (m / 2) * (2 * 2)) with ((2 * (m / 2)) * (2 * (m / 2))) by ring.
  apply Z.square_le_mono_nonneg; [auto | apply Z.mul_div_le; omega].
  replace 0 with (2 * 0) by ring.
  apply Zmult_le_compat_l; [apply Zdiv_le_lower_bound | auto]; omega.
Qed.

Lemma descent_inequality: forall m,
    m > 0 -> (m / 2) * (m / 2) + (m / 2) * (m / 2) < m * m.
Proof.
  intros m m_gt_0.
  cut (((m * m) / 4) + (m * m) / 4 < m * m).
  intros Cut.
  remember (square_le_lemma m m_gt_0).
  omega.
  cut ((m * m / 4 + m * m / 4) <= (m * m / 2)).
  intros Cut.
  apply (Z.le_lt_trans _ (m * m / 2) _ Cut).
  apply Z_div_lt; [omega | apply Zmult_gt_0_compat; auto].
  replace ((m * m / 4) + (m * m / 4)) with (2 * (m * m / 4)) by ring.
  apply Zdiv_le_lower_bound; [omega | auto].
  replace (2 * (m * m / 4) * 2) with (4 * (m * m / 4)) by ring.
  apply Z_mult_div_ge; omega.
Qed.

Lemma N_gt_0: forall a b q N,
  (a > 0 \/ b > 0) ->
  q > 0 ->
  N = (a * a + b * b) ->
  (q | N) ->
  N > 0.
Proof.
  intros a b q N a_or_b_gt_0 q_gt_0 def_N q_divides_N.
  apply (sum_of_squares_positive a b N a_or_b_gt_0 def_N).
Qed.

Lemma m_gt_0: forall a b q N m,
  (a > 0 \/ b > 0) ->
  q > 0 ->
  N = (a * a + b * b) ->
  (q | N) ->
  m = N / q ->
  m > 0.
Proof.
  intros a b q N m a_or_b_gt_0 q_gt_0 def_N q_divides_N def_m.
  rewrite def_m; apply (div_positive q N q_gt_0); auto.
  apply (N_gt_0 a b q); auto.
Qed.

Theorem descent_smaller: forall a b q N m,
  (a > 0 \/ b > 0) ->
  q > 0 ->
  N = (a * a + b * b) ->
  (q | N) ->
  m = N / q ->
  forall k t1 t2,  (k, t1, t2) = descent a b q ->
  k = 1 \/ (k < m).
Proof.
  intros a b q N m a_or_b_gt_0 q_gt_0 def_N q_div_N def_m k u v.
  unfold descent.
  rewrite <- def_N, <- def_m.
  destruct (Z.eq_dec m 1); intros descent_def; inversion descent_def.
  - left; reflexivity.
  - right.
    rewrite <- (Z.abs_square (descent_modulus a m)).
    rewrite <- (Z.abs_square (descent_modulus b m)).
    Search (_ < _ -> _ > _).
    remember ((m_gt_0 a b q N m a_or_b_gt_0 q_gt_0 def_N q_div_N def_m)) as m_gt_0.
    apply Z.div_lt_upper_bound; [apply Z.gt_lt; apply m_gt_0; auto | auto].
    remember (descent_modulus_le_m_div_2 a m m_gt_0).
    remember (descent_modulus_le_m_div_2 b m m_gt_0).
    assert ((Z.abs (descent_modulus a m)) *
            (Z.abs (descent_modulus a m)) <= (m / 2) * (m / 2)).
    apply Z.square_le_mono_nonneg; [apply Z.abs_nonneg | auto].
    assert ((Z.abs (descent_modulus b m)) *
            (Z.abs (descent_modulus b m)) <= (m / 2) * (m / 2)).
    apply Z.square_le_mono_nonneg; [apply Z.abs_nonneg | auto].
    assert (Z.abs (descent_modulus a m) *
            Z.abs (descent_modulus a m) +
            Z.abs (descent_modulus b m) *
            Z.abs (descent_modulus b m) <= (m / 2) * (m / 2) + (m / 2) * (m / 2)) by omega.
    apply (Z.le_lt_trans _ _ _ H4).
    apply descent_inequality; auto.
Qed.

Lemma diophantine_identity:
  forall a b c d, (a * a + b * b) * (c * c + d * d) = (a * c + b * d) * (a * c + b * d) + (b * c - a * d) * (b * c - a * d).
Proof.
  intros; ring.
Qed.

Lemma descent_div_sum: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (descent_modulus a m * descent_modulus a m + descent_modulus b m * descent_modulus b m)).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  assert (m > 0) as m_gt_0.
  rewrite def_m; apply div_positive; auto.
  rewrite <- Z.mod_divide; [|omega].
  rewrite Zplus_mod.
  repeat rewrite (Zmult_mod (descent_modulus a m) (descent_modulus a m) m), descent_modulus_equiv_a_mod_m; [|omega].
  repeat rewrite (Zmult_mod (descent_modulus b m) (descent_modulus b m) m), descent_modulus_equiv_a_mod_m; [|omega].
  repeat rewrite <- Zmult_mod.
  rewrite <- Zplus_mod.
  rewrite Z.mod_divide; [auto | omega].
  exists q.
  rewrite def_m, def_N.
  apply Zdivide_Zdiv_eq; [omega | auto].
  rewrite <- def_N; auto.
Qed.

Lemma descent_div_N: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) -> (m | N).
Proof.
  intros a b q N m q_gt_0 N_gt_0 def_N def_m q_div_N.
  exists q.
  rewrite def_m.
  apply Zdivide_Zdiv_eq; [omega | auto].
Qed.

(*
  (u * u + v * v) / m * q =
  (a * u + b * v) / m * ((a * u + b * v) / m) + (a * v - b * u) / m * ((a * v - b * u) / m)
 *)

Lemma descent_div_term1: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (a * descent_modulus a m + b * descent_modulus b m)).
Admitted.

Lemma descent_div_term2: forall a b q N m,
  q > 0 -> N > 0 ->
  N = (a * a + b * b) ->
  m = N / q ->
  (q | N) ->
  (m | (b * descent_modulus a m - a * descent_modulus b m)).
Admitted.

Compute (descent 5 1 13).
Compute (5 * 13).
Compute (1 * 1 + 5 * 5).

Compute (descent 12 1 29).
Compute (descent (-7) 3 29).
Compute (descent 442 1 953).
Compute (descent 69 2 953).
Compute (descent (-15) (-41) 953).

Lemma div_swap_l: forall a b c, a <> 0 -> (a | b) -> b = a * c <-> b / a = c.
Proof.
  intros a b c a_neq_0 a_div_b.
  split.
  - destruct a_div_b as [x def_a].
    intros def_b.
    rewrite def_a.
    rewrite Z_div_mult_full; auto.
    rewrite def_a, Z.mul_comm in def_b.
    rewrite Z.mul_cancel_l in def_b; auto.
  - intros def_b.
    rewrite <- def_b.
    Search (_ * (_ / _)).
    rewrite <- Z.divide_div_mul_exact; auto.
    Search (_ * _ / _).
    rewrite Z.mul_comm.
    symmetry.
    apply Z_div_mult_full; auto.
Qed.

Lemma descent_mult_key_lemma: forall t0 t1 m a,
    (m | t0) ->
    (m | t1) ->
    (t0 / m * (t0 / m) + t1 / m * (t1 / m) = a) = (t0 * t0 + t1 * t1 = m * m * a).
Proof.
  intros t0 t1 m a m_div_t0 m_div_t1.
  symmetry.
  (* setoid rewrite fails here for some reason I don't understand *)
  (* rewrite (div_swap_l (m * m) (t0 * t0 + t1 * t1) a). *)
Admitted.

Theorem descent_mult: forall a b q N,
    q > 0 -> N > 0 -> N = (a * a + b * b) -> (q | N) ->
    forall k r s,
      (k, r, s) = descent a b q ->
      k * q = r * r + s * s.
Proof.
  intros a b q N.
  intros q_gt_0 N_gt_0 def_N q_div_N.
  intros k r s descent_def.
  unfold descent in descent_def.
  rewrite <- def_N in descent_def.
  remember (N / q) as m.
  assert (m > 0) as m_gt_0.
  rewrite Heqm; apply div_positive; auto.
  destruct (Z.eq_dec m 1); inversion descent_def.
  - destruct q_div_N as [x def_N_with_q].
    rewrite Z.mul_1_l, <- def_N, def_N_with_q.
    rewrite e, def_N_with_q in Heqm.
    rewrite Z_div_mult_full in Heqm; [auto | omega].
    symmetry in Heqm.
    rewrite Heqm, Z.mul_1_l; reflexivity.
  - remember (descent_modulus a m) as u.
    remember (descent_modulus b m) as v.
    remember (descent_div_sum a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as m_div_u_v.
    destruct m_div_u_v as [x m_div_u_v].
    assert ((u * u + v * v)*(a * a + b * b) = m * m * x * q) as H.
    destruct Heqm_div_u_v.
    rewrite <- Hequ, <- Heqv in m_div_u_v.
    rewrite Z.gt_lt_iff in q_gt_0.
    destruct q_div_N as [y def_N_with_q].
    rewrite def_N_with_q, Z_div_mult_full in Heqm; [auto | omega].
    rewrite <- Heqm in def_N_with_q.
    rewrite <- def_N, m_div_u_v, def_N_with_q.
    ring.
    rewrite Z.mul_comm in H at 1.
    rewrite diophantine_identity in H.
    replace ((a * u + b * v) * (a * u + b * v) + (b * u - a * v) * (b * u - a * v) = m * m * x * q) with (((a * u + b * v) / m) * ((a * u + b * v) / m) + ((b * u - a * v) /m) * ((b * u - a * v) /m) = x * q) in H.
    rewrite H.
    (* did this already, do it again *)
    (* TODO: must clean up *)
    destruct Heqm_div_u_v.
    rewrite <- Hequ, <- Heqv in m_div_u_v.
    remember (descent_div_sum a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as m_div_u_v2.
    destruct Heqm_div_u_v2.
    rewrite <- Hequ, <- Heqv in m_div_u_v2.
    Search (_ * _ = _ * _).
    rewrite Z.mul_cancel_r; [ | omega].
    apply div_swap_l; [omega | | rewrite (Z.mul_comm x m) in m_div_u_v]; auto.
    (* must swap m * m over to the other side and redistribute *)
    rewrite <- H1, <- H2.
    replace ((a * u + b * v) * (a * u + b * v) + (b * u - a * v) * (b * u - a * v) = m * m * x * q) with (((a * u + b * v) / m) * ((a * u + b * v) / m) + ((b * u - a * v) / m) * ((b * u - a * v) / m) = x * q).
    rewrite <- H1, <- H2; reflexivity.
    remember (descent_div_term1 a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as div_t0.
    remember (descent_div_term2 a b q N m q_gt_0 N_gt_0 def_N Heqm q_div_N) as div_t1.
    remember (a * u + b * v) as t0.
    remember (b * u - a * v) as t1.
    destruct Heqdiv_t0.
    destruct Heqdiv_t1.
    rewrite <- Hequ, <- Heqv, <- Heqt0 in div_t0.
    rewrite <- Hequ, <- Heqv, <- Heqt1 in div_t1.
    replace (m * m * x * q) with (m * m * (x * q)) by ring.
    apply descent_mult_key_lemma; auto.
Qed.

Theorem p_sumofsquares: forall p x y, prime p -> x * x + y * y = p <-> p mod 4 = 1.
Proof.
  intros p x y p_prime.
  split.
  intros p_sumofsquares.
