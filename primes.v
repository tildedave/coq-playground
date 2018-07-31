Require Import PeanoNat NArith.
Require Coq.Program.Wf.
Require Import Omega.

(* https://stackoverflow.com/questions/33302526/well-founded-recursion-in-coq *)
Require Coq.Program.Tactics.

Fixpoint count_up (m : nat) (inc : nat) : nat :=
  match inc with
  | 0 => m
  | (S p) => 1 + count_up m p
  end.

Goal forall m inc, count_up m inc = m + inc.
  induction inc.
  simpl; auto.
  simpl.
  rewrite IHinc.
  auto.
Qed.

Fixpoint find_factor_helper (m n i : nat) : nat :=
  match i with
    0 => n
  | 1 => n
  | (S p) => (if (Nat.eq_dec (n mod m) 0) then
                m
              else find_factor_helper (m + 1) n p)
  end.

Definition find_factor (n : nat) : nat := find_factor_helper 2 n n.

Lemma a_mod_a_eq_0: forall a, a mod a = 0.
Proof.
  intros; auto.
  destruct (Nat.eq_dec a 0). rewrite e; simpl; auto.
  apply Nat.mod_same in n; auto.
Qed.

Lemma find_factor_helper_mult : forall i m n b, 1 < m -> (find_factor_helper m n i) = b -> n mod b = 0.
  induction i.
  intros m n b m_gt_1.
  simpl.
  intros n_eq_b; rewrite n_eq_b.
  apply a_mod_a_eq_0.
  intros m n b m_gt_1.
  intros FindFactor.
  unfold find_factor_helper in FindFactor.
  destruct (Nat.eq_dec i 0) as [i_eq_0 | i_neq_0].
  rewrite i_eq_0 in FindFactor.
  rewrite FindFactor; apply a_mod_a_eq_0.
  destruct (Nat.eq_dec (n mod m) 0) as [n_mod_m_eq_0 | n_mod_m_neq_0].
  destruct i in FindFactor.
  rewrite <- FindFactor; apply a_mod_a_eq_0.
  rewrite <- FindFactor; auto.
  fold find_factor_helper in FindFactor.
  remember (find_factor_helper (m + 1) n i) as c.
  symmetry in Heqc.
  assert (m + 1 > 1). Search (_ + _ > _). omega.
  apply (IHi _ _ _ H) in Heqc.
  destruct i in FindFactor.
  rewrite FindFactor. apply a_mod_a_eq_0.
  rewrite <- FindFactor; auto.
Qed.

Lemma find_factor_helper_1_lt : forall i m n b, 1 < n -> 1 < m -> (find_factor_helper m n i) = b -> 1 < b.
  induction i.
  intros m n b n_neq_0 m_gt_0 FindFactor.
  simpl in FindFactor.
  rewrite <- FindFactor; auto.
  intros m n b n_neq_0 m_gt_0 FindFactor.
  unfold find_factor_helper in FindFactor.
  destruct (Nat.eq_dec (n mod m) 0) as [n_mod_m_eq_0 | n_mod_m_neq_0].
  destruct i in FindFactor.
  rewrite <- FindFactor; auto.
  rewrite <- FindFactor. auto.
  fold find_factor_helper in FindFactor.
  remember (find_factor_helper (m + 1) n i) as c.
  inversion FindFactor.
  symmetry in Heqc.
  assert (1 < m + 1) as One_lt_m_plus. auto with arith.
  apply (IHi _ _ _ n_neq_0 One_lt_m_plus) in Heqc.
  destruct i; auto; auto.
Qed.

Theorem find_factor_mult: forall n b, 1 < n -> find_factor n = b -> (n / b) * b = n.
  intros n b n_lt_1.
  intros FindFactor.
  unfold find_factor in FindFactor.
  assert (1 < 2) as H1_lt_2; auto.
  assert (b <> 0) as b_neq_0.
  apply (find_factor_helper_1_lt _ _ _ _ n_lt_1 H1_lt_2) in FindFactor; omega.
  apply (find_factor_helper_mult _ _ _ _ H1_lt_2) in FindFactor.
  Search (_ mod _ = 0).
  apply (Nat.div_exact n b b_neq_0) in FindFactor.
  rewrite Nat.mul_comm.
  auto.
Qed.

Theorem find_factor_1_lt : forall n b, 1 < n -> find_factor n = b -> 1 < b.
Proof.
  intros n b H1_lt_n FindFactor.
  unfold find_factor in FindFactor.
  assert (1 < 2) as H1_lt_2; auto.
  apply (find_factor_helper_1_lt n 2 n _ H1_lt_n H1_lt_2); auto.
Qed.

Require Import List.
Import ListNotations.

Program Fixpoint prime_divisors_helper (n i : nat) : (list nat) :=
  match i with
  | 0 => []
  | (S p) => (
      match n with
      | 0 => []
      | 1 => []
      | _ => let a := find_factor n in
             if (Nat.eq_dec a n) then
               [n]
             else
               a :: prime_divisors_helper (n / a) p
      end
    )
  end.

Program Fixpoint prime_divisors (n : nat) : (list nat) :=
  prime_divisors_helper n n.

Compute (prime_divisors 8).

Fixpoint mult_list (l : list nat) :=
  match l with
  | [] => 1
  | a :: l => a * (mult_list l)
  end.

Compute (mult_list (prime_divisors 16)).

Lemma prime_divisors_helper_1_lt : forall i n x l, prime_divisors_helper n i = x :: l -> x > 1.
Proof.
  induction i.
  intros n x l.
  simpl; discriminate.
  intros n x l.
  intros def_of_x.
  unfold prime_divisors_helper in def_of_x.
  remember (find_factor n) as a.
  fold (prime_divisors_helper (n / a) i) in def_of_x.
  destruct (Nat.eq_dec a n).
  destruct n; [discriminate | destruct n].
  discriminate.
  inversion def_of_x.
  auto with arith.
  destruct n; [discriminate | destruct n].
  discriminate.
  inversion def_of_x.
  unfold gt.
  symmetry in Heqa.
  rewrite <- H0.
  apply (find_factor_1_lt (S (S n)) a).
  auto with arith.
  assumption.
Qed.

Goal forall i n x l, n <= i -> prime_divisors_helper n i = (x :: l) -> n = x * (n / x).
  induction i.
  intros n x l.
  intros n_lte_i def_of_x.
  Search (_ * (_ / _)).
  apply Nat.div_exact.
  Search (_ <> 0).
  apply Nat.neq_0_lt_0.
  Search (S _ < _ -> _ < _).
  apply Nat.lt_succ_l.
  apply (prime_divisors_helper_1_lt 0 n x l); assumption.
  unfold prime_divisors_helper in def_of_x; discriminate.
  intros n x l n_lte_i def_of_x.
  unfold prime_divisors_helper in def_of_x.
  remember (find_factor n) as a.
  fold (prime_divisors_helper (n / a) i) in def_of_x.
  destruct n.
  discriminate.
  destruct n.
  discriminate.
  destruct (Nat.eq_dec a (S (S n))).
  inversion def_of_x.
  rewrite H0.
  Search (_ * (_ / _)).
  apply Nat.div_exact. rewrite <- H0. auto with arith.
  apply a_mod_a_eq_0.
  inversion def_of_x.
  destruct l.

  apply IHi (S (S n) / x).

  rewrite n_eq_0; apply Nat.mod_0_l.

  intro PrimeDivisors.
  unfold prime_divisors in PrimeDivisors.
  Search (Wf.Fix_sub).
  apply Wf.Fix_eq in PrimeDivisors.

  destruct (Nat.eq_dec (find_factor recarg) recarg) in PrimeDivisors.

  Goal forall n, mult_list (prime_divisors n) = n.
  intros.
