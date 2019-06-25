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
Lemma H4_not_0: (4 <> 0). omega. Qed.
Lemma H2_div_4: (2 | 4). apply (Zdivide_intro _ _ 2); omega. Qed.

Lemma sq_mod_4: forall a, a * a mod 4 = 0 -> (2 | a).
Proof.
  intros a a_sq_mod_4.
  apply (Zmod_divide _ _ H4_not_0) in a_sq_mod_4.
  apply (Zdivide_trans 2 4 (a * a) H2_div_4) in a_sq_mod_4.
  apply (prime_mult 2 prime_2) in a_sq_mod_4; destruct a_sq_mod_4; auto.
Qed.

Theorem p_sumofsquares_easy: forall p x y, prime p -> x * x + y * y = p -> p mod 4 = 1.
Proof.
  intros p x y p_prime p_sumofsquares.

  cut ((x*x + y*y) mod 4 = p mod 4).
  intros Cut.
  Check Z.add_mod.
  destruct (mod_4 (x*x + y*y)) as [H | [H | [H | H]]];
    rewrite (Z.add_mod _ _ _ H4_not_0) in H;
    destruct (mod_4 (x*x)) as [Hx | [Hx | [Hx | Hx]]];
    destruct (mod_4 (y*y)) as [Hy | [Hy | [Hy | Hy]]];
    rewrite Hx, Hy in H;
    compute in H;
    inversion H.
  (* these are the non-ridiculous hypothesis.
     however several of them imply a common divisor between x and y *)




  destruct (mod_4 (y*y)).
  (* this is the case where x and y share a factor and so p is not prime *)


  rewrite p_sumofsquares; auto.
auto.
  intros Cut.
  Focus 2.
  rewrite p_sumofsquares; auto.

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
