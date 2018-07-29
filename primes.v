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

Fixpoint find_factor (n : nat) : nat := find_factor_helper 2 n n.

(*
Program Fixpoint factors (n : Z) (H : n > 0) : list Z :=
  find_factor n n H
 *)

Lemma a_mod_nonzero : forall a b, a mod b <> 0 -> b <> 0 -> a <> 0.
  intros a b AModB_NotZero BNotZero.
  Search (?a <> 0 -> _ mod _ = _).
  rewrite Nat.mod_eq in AModB_NotZero.
  assert (b > 0). omega.
  unfold not.
  intros AIsZero.
  rewrite AIsZero in AModB_NotZero.
  simpl in AModB_NotZero.
  contradict AModB_NotZero.
  auto.
  auto.
Qed.

Fixpoint find_factor (m : nat) (n : nat) : nat :=
  match m with
    0 => n
  | 1 => n
  | (S p) => (if (Nat.eq_dec (n mod m) 0) then
                m
              else find_factor p n)
  end.

Compute (find_factor 12 15).

Theorem find_factor_mult : forall a n b, n <> 0 -> (find_factor a n) = b -> n mod b = 0.
  intros a n b N_NonZero.
  induction a.
  intro FindFactor.
  simpl in FindFactor; rewrite <- FindFactor.
  apply Nat.mod_same in N_NonZero; auto.
  intros FindFactor.
  unfold find_factor in FindFactor.
  destruct (Nat.eq_dec (n mod S a) 0) as [H_Sa_Divides | H_Sa_NotDivides].
  destruct a.
  apply Nat.mod_same in N_NonZero; auto.
  rewrite FindFactor in H_Sa_Divides; auto.
  fold find_factor in FindFactor.
  destruct a.
  apply Nat.mod_same in N_NonZero; auto.
  apply IHa in FindFactor; auto.
Qed.

Lemma cut : forall j k : nat, j <> 0 -> j mod k = 0 -> j > k.
Proof.
  intros j k.
  intros J_NonZero J_ModK_Zero.
  Search (_ mod _ = 0).
  destruct k.
  apply Nat.neq_0_lt_0 in J_NonZero; auto.
  assert (S k <> 0); auto with arith.
  apply (Nat.mod_divides j (S k) H) in J_ModK_Zero.
  destruct J_ModK_Zero as [q H1].
  assert (j > 0 /\ S k > 0). omega.
  rewrite H1 in H0.
  unfold gt in H0.
  destruct H0.
  Search (_ < _ * _).
  apply Nat.lt_0_mul' in H0.
  destruct H0.
  unfold gt.
  rewrite H1.
  Search (_ < _ * _).
Admitted.

Theorem find_factor_decreasing : forall a b n, n <> 0 -> (find_factor a n) = b -> b <= n.
Proof.
  intros a b n N_NonZero.
  induction a.
  simpl; omega.
  unfold find_factor.
  fold find_factor.
  destruct (Nat.eq_dec (n mod (S a)) 0) as [H_Sa_Divides | H_Sa_NotDivides].
  assert (S a <> 0) as Sa_NonZero; auto.
  apply (cut _ _ N_NonZero) in H_Sa_Divides.
  intro.
  destruct H.
  destruct a; auto.
  omega.
  destruct a; auto.
Qed.

Theorem find_factor_gt_1 : forall a n, n > 1 -> find_factor a n > 1.
Proof.
  induction a.
  intros n N_NonZero.
  simpl; auto.
  unfold find_factor.
  fold find_factor.
  intros n n_gt_1.
  destruct (Nat.eq_dec (n mod (S a)) 0) as [sa_Divides | sa_NotDivides].
  case a. auto. intros; omega.
  destruct a. auto.
  apply IHa in n_gt_1; auto.
Qed.

Require Import List.
Import ListNotations.

Program Fixpoint prime_divisors (n : nat) { measure n } : (list nat) :=
  match n with
    0 => []
  | 1 => []
  | (S p) => let a := find_factor p n in
             if (Nat.eq_dec a n) then
               [n]
             else
               a :: prime_divisors (n / a)
  end.
Obligation 1.
remember (find_factor p (S p)) as b.
assert (S p > 1) as Sp_gt_1. omega.
apply (find_factor_gt_1 p (S p)) in Sp_gt_1.
rewrite <- Heqb in Sp_gt_1.
unfold gt in Sp_gt_1.
assert (0 < S p).
apply Nat.lt_0_succ.
apply (Nat.div_lt _ _ H1 Sp_gt_1).
Defined.

Compute (prime_divisors 16).

Compute (prime_divisors 8).
Compute (find_factor 8).
