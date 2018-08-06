Require Import PeanoNat NArith.
Require Coq.Program.Wf.
Require Import Omega.

(* https://stackoverflow.com/questions/33302526/well-founded-recursion-in-coq *)
Require Coq.Program.Tactics.

Section find_factor.

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

End find_factor.

Section prime_divisors.
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

  Definition prime_divisors (n : nat) : (list nat) := prime_divisors_helper n n.

  Compute (prime_divisors 8).

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

  Lemma prime_divisors_helper_mult : forall i n x l, n <= i -> prime_divisors_helper n i = (x :: l) -> n = x * (n / x).
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
    inversion def_of_x as [a_eq_x].
    symmetry in Heqa; apply find_factor_mult in Heqa; symmetry in Heqa.
    rewrite <- a_eq_x; rewrite Nat.mul_comm. assumption.
    auto with arith.
  Qed.

  Theorem prime_divisors_mult : forall n x l, prime_divisors n = x :: l -> n = x * (n / x).
    intros n x l def_of_x_l.
    unfold prime_divisors in def_of_x_l.
    apply (prime_divisors_helper_mult n n x l).
    auto with arith. assumption.
  Qed.

  Lemma prime_divisors_helper_trivial : forall h, [] = prime_divisors_helper 1 h.
  Proof.
    intro h; unfold prime_divisors_helper; destruct h; reflexivity; reflexivity.
  Qed.

  Lemma prime_divisors_helper_inversion : forall i n x l, n <= (S i) -> prime_divisors_helper n (S i) = x :: l -> x = find_factor n /\ ((l = prime_divisors_helper (n / x) i /\ x <> n) \/ (l = [] /\ x = n)).
    intros i n x l n_lte_Si def_of_x_l.
    unfold prime_divisors_helper in def_of_x_l.
    remember (find_factor n) as a.
    fold (prime_divisors_helper (n / a) i) in def_of_x_l.
    destruct n.
    discriminate.
    destruct n.
    discriminate.
    destruct (Nat.eq_dec a (S (S n))) as [a_eq | a_neq].
    inversion def_of_x_l.  symmetry in a_eq.
    split.
    - exact a_eq.
    - replace (S (S n) / S (S n)) with 1.
      replace (prime_divisors_helper 1 i) with ([] : list nat).
      right. split ; [reflexivity | reflexivity].
      apply prime_divisors_helper_trivial.
      symmetry.
      apply (Nat.div_same).
      auto with arith.
    - split.
      inversion def_of_x_l. reflexivity.
      inversion def_of_x_l.
      rewrite H1.
      left.
      split ; [ reflexivity | rewrite <- H0 ; assumption ].
  Qed.

  Lemma prime_divisors_helper_inversion2 : forall i n, n <= (S i) -> prime_divisors_helper n i = [] -> i = 0 \/ n <= 1.
    intros i n n_lte_Si H.
    destruct i.
    left; reflexivity.
    right.
    unfold prime_divisors_helper in H.
    destruct n.
    omega.
    destruct n.
    omega.
    remember (find_factor (S (S n))) as a.
    destruct (Nat.eq_dec a (S (S n))).
    discriminate.
    discriminate.
  Qed.

  Check prime_divisors.
End prime_divisors.

Section correctness_of_prime_divisors.
  Require Import List.

  Import ListNotations.

  Fixpoint mult_list (l : list nat) :=
    match l with
    | [] => 1
    | a :: l => a * (mult_list l)
    end.

  Compute (mult_list (prime_divisors 16)).

  Lemma prime_divisors_helper_equiv_mult_list : forall l i n, 1 < n <= i -> l = prime_divisors_helper n i -> mult_list l = n.
  Proof.
    induction l.
    intros i n n_bounded Heql.
    symmetry in Heql.
    apply prime_divisors_helper_inversion2 in Heql.
    destruct Heql; [omega | simpl ; omega].
    omega.
    intros i n n_bounded Heql.
    symmetry in Heql.
    destruct i.
    simpl in Heql; discriminate.
    (* prime_divisors_helper_inversion is not helping me because it forces me to apply the IH criteria bounds in cases where no recursion was done *)
    apply prime_divisors_helper_inversion in Heql.
    destruct Heql as [def_of_a [[def_of_l a_neq_n] | [def_of_l a_eq_n]]].
    simpl.
    cut (1 < n / a <= i).
    intros Cut.
    rewrite (IHl _ _ Cut def_of_l).
    symmetry in def_of_a. rewrite Nat.mul_comm. apply find_factor_mult ; [ omega | auto ].
    assert (1 < a) as a_gt_1. symmetry in def_of_a. apply (find_factor_1_lt n a) in def_of_a ; [omega |omega].
    symmetry in def_of_a. apply find_factor_mult in def_of_a ; [ auto | omega].
    assert (~(n < a)).
    unfold not.
    contradict a_neq_n.
    apply Nat.div_small in a_neq_n.
    rewrite a_neq_n in def_of_a; omega.
    assert (a < n) as a_lt_n. omega.
    split.
    (*
    1 < n / a because...
      it cannot be 0 because a < n
      it cannot be 1 because a <> n and n / a * a = n so a fully divides n
     *)
    assert (~(n / a = 0 \/ n / a = 1)).
    unfold not.
    intros C.
    destruct C as [n_div_a_eq_0 | n_div_a_eq_1].
    rewrite n_div_a_eq_0 in def_of_a; omega.
    rewrite n_div_a_eq_1 in def_of_a; omega.
    omega.
    (*
    n / a <= i because...
      a < n
      So n / a < n (because 1 < a)
      So n / a < S i
      So n / a <= i
     *)
    Search (_ < S _).
    Search (S _ <= S _).
    apply (Nat.div_lt n a) in a_gt_1.
    Search (_ < _ -> _ <= _ -> _).
    destruct n_bounded as [n_gt_1 n_le_Si].
    apply (Nat.lt_le_trans _ _ _ a_gt_1) in n_le_Si.
    apply lt_n_Sm_le; assumption.
    omega.
    (* non-recursive time :) *)
    rewrite def_of_l.
    simpl.
    rewrite Nat.mul_1_r; auto.
    omega.
  Qed.

  Theorem prime_divisors_equiv_mult_list : forall n, 1 < n -> mult_list (prime_divisors n) = n.
  Proof.
    intros n n_bounded.
    unfold prime_divisors.
    remember (prime_divisors_helper n n) as l.
    apply (prime_divisors_helper_equiv_mult_list _ n n) ; [ omega | assumption ].
  Qed.

  (*
     If find_factor_helper m n i = x
     AND
     We didn't hit the '0' or '1' condition on i
     AND
     We basically need to have hit the n mod m = 0 condition.
     THEN
     There's no element between initial m and result that satisfies n mod m = 0.
   *)

  Lemma find_factor_helper_returns_first_divisor :
    forall i m n x,
      i = n - m + 2 ->
      m <= n ->
      find_factor_helper m n i = x ->
      n mod x = 0 ->
      forall a, m <= a < x -> n mod a <> 0.
    induction i.
    intros; omega.
    destruct i.
    intros; omega.
    intros m n x i_bounded m_bounded def_of_x n_divides_x.
    unfold find_factor_helper in def_of_x.
    fold (find_factor_helper (m + 1) n (S i)) in def_of_x.
    destruct (Nat.eq_dec n m) as [m_eq_n | m_neq_n].
    rewrite m_eq_n in def_of_x.
    rewrite a_mod_a_eq_0 in def_of_x.
    simpl in def_of_x.
    intros a; omega.
    destruct (Nat.eq_dec (n mod m) 0) as [m_div_n | m_not_div_n].
    intros a; omega.
    assert ((S i) = n - (m + 1) + 2) as H1. omega.
    assert (m + 1 <= n) as H2. omega.
    remember (IHi (m + 1) _ x H1 H2 def_of_x n_divides_x) as J.
    intros a.
    intros a_bounded.
    destruct a_bounded as [m_lt_a a_lt_x].
    unfold lt in m_lt_a.
    Search (_ <= _ -> _ \/ _).
    apply le_lt_or_eq in m_lt_a.
    destruct m_lt_a as [Sm_lt_a | Sm_eq_a].
    apply J; omega.
    rewrite Sm_eq_a in m_not_div_n.
    assumption.
  Qed.

End correctness_of_prime_divisors.
