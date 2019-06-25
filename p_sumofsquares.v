Require Import Znumtheory Zdiv ZArith.
Local Open Scope Z_scope.

Search prime.
Search Zdivide.

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
  Search (~ prime _).
  Search (prime _).
  intros p_prime.
  Search (prime _).
  remember (prime_divisors p p_prime a p_mod_0); omega.
Qed.

Lemma mod_4_eq_2_not_prime: forall p, 2 < p -> p mod 4 = 2 -> ~ prime p.
Proof.
  intros p H1_lt_p.
  Search (_ mod _ = _ -> (_ | _)).
  intros Hp_mod.
  apply (Zmod_divide_minus _ _ _ H0_lt_4) in Hp_mod.
  destruct Hp_mod as [d hp].
  Search (_ - _ = _).
  rewrite Z.sub_move_r in hp.
  replace (d * 4 + 2) with ((d * 2 + 1) * 2) in hp; [auto | omega].
  Search (~ prime _).
  cut (p mod 2 = (d * 2 + 1) * 2 mod 2); [auto | rewrite hp; reflexivity].
  intros Cut.
  Search (_ * _ mod _ = 0).
  rewrite Z_mod_mult in Cut.
  apply (mod_0_not_prime p 2); [omega | exact Cut].
Qed.

Lemma mod_2_4: 2 mod 4 = 2. compute; reflexivity. Qed.

(* p > 4 makes the proof easier.
   p = 3 can't be written as a sum of squares and p = 1 isn't prime. *)
Theorem p_sumofsquares_easy: forall p x y, prime p -> p > 4 -> p = x * x + y * y -> p mod 4 = 1.
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
    prime p -> p mod 4 = 1 -> exists x y, (p | x^2 + y^2) /\ Zgcd x y = 1.
Admitted.

Lemma p_descent: forall p x y, prime p -> (p | x^2 + y^2) /\ Zgcd x y = 1 -> exists a b, p = a^2 + b^2 /\ Zgcd a b = 1.
Admitted.

Theorem p_sumofsquares: forall p x y, prime p -> x^2 + y^2 = p <-> p mod 4 = 1.
Proof.
  intros p x y p_prime.
  split.
  intros p_sumofsquares.
