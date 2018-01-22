Require Import List Arith BinNat.
Import ListNotations.

Inductive digit : Set :=
| Digit : forall n, n < 10 -> digit.

Definition denoteDigit (d : digit) : nat :=
  match d with Digit n _ => n end.

Definition denotePair p :=
  match p with
    (d1, d2) => 10 * (denoteDigit d1) + (denoteDigit d2)
  end.

Definition denoteDigitList (dl : list digit) : nat :=
  fold_left (fun n d => (n * 10) + (denoteDigit d)) dl 0.

Definition D0 : digit.
  refine (Digit 0 _).
  auto with arith.
Defined.

Definition D1 : digit.
  refine (Digit 1 _).
  auto with arith.
Defined.

Definition D2 : digit.
  refine (Digit 2 _).
  auto with arith.
Defined.

Definition D3 : digit.
  refine (Digit 3 _).
  auto with arith.
Defined.

Definition D4 : digit.
  refine (Digit 4 _).
  auto with arith.
Defined.

Definition D5 : digit.
  refine (Digit 5 _).
  auto with arith.
Defined.

Definition D6 : digit.
  refine (Digit 6 _).
  auto with arith.
Defined.

Definition D7 : digit.
  refine (Digit 7 _).
  auto with arith.
Defined.

Definition D8 : digit.
  refine (Digit 8 _).
  auto with arith.
Defined.

Definition D9 : digit.
  refine (Digit 9 _).
  auto with arith.
Defined.

Compute (denoteDigitList [D3 ; D4 ; D7]).

Definition toDigit (n : nat | n < 10) : digit.
  inversion n.
  intros.
  exact (Digit x H).
Defined.

Lemma all_nat_gte_zero : forall m, m >= 0.
  intros.
  induction m.
  auto.
  auto with arith.
Qed.

Lemma mod_is_lt : forall (m n : nat), n > 0 -> (m mod n) < n.
  intros.
  apply (Nat.mod_bound_pos m n (all_nat_gte_zero m)).
  exact H.
Qed.

Lemma denoteDigit_is_lt_10 : forall (d : digit), denoteDigit d < 10.
  intros.
  unfold denoteDigit.
  elim d.
  intros.
  exact l.
Qed.

Lemma blah : forall (a b c d : nat), a < d -> d + b <= c -> a + b < c.
Proof.
  intros.
  - apply (lt_le_trans (a + b) (d + b) c).
    apply (plus_lt_compat_r a d b H).
    assumption.
Qed.

Definition addDigit (d1 : digit) (d2 : digit) : (digit * digit).
  pose (m := denoteDigit d1).
  pose (n := denoteDigit d2).
  destruct (lt_dec (m + n) 10) as [ TotalLt10 | TotalGt10 ].
  exact (D0, Digit (m + n) TotalLt10).
  assert (m + n < 19) as SumMinus20.

  assert (m < 10). apply denoteDigit_is_lt_10.
  assert (n < 10). apply denoteDigit_is_lt_10.

  apply (blah m n _ 10 H).
  rewrite plus_comm.
  apply (plus_lt_compat_r n 10 10) in H0.
  auto with arith.
  apply lt_le_S in SumMinus20.
  apply (minus_le_compat_r _ _ 10) in SumMinus20.
  apply not_lt in TotalGt10.
  unfold ge in TotalGt10.
  rewrite (Nat.sub_succ_l 10 (m + n) TotalGt10) in SumMinus20.
  apply (le_S_gt _ (19 - 10)) in SumMinus20.
  unfold gt in SumMinus20.
  apply Nat.lt_lt_succ_r in SumMinus20.
  assert (S (19 - 10) = 10).
  auto with arith.
  rewrite H in SumMinus20.
  exact (D1, Digit (m + n - 10) SumMinus20).
Defined.

Compute (denotePair (addDigit D3 D4)).

Theorem addDigit_works_as_expected :
  forall d1 d2 : digit,
          (denoteDigit d1) + (denoteDigit d2) = (denotePair (addDigit d1 d2)).
Proof.
  intros.
  unfold denotePair.
  unfold denoteDigit.
  unfold addDigit.
  destruct (lt_dec (denoteDigit d1 + denoteDigit d2) 10).
  auto with arith.
  assert (10 * (match D1 with | Digit n0 _ => n0 end) = 10) as Ten.
  auto.
  rewrite Ten.
  apply not_lt in n.
  unfold ge in n.
  Search (_ + _ - _).
  rewrite (Nat.add_sub_assoc _ _ 10 n).
  assert (10 + (denoteDigit d1 + denoteDigit d2) - 10 = (denoteDigit d1 + denoteDigit d2)).
  auto with arith.
  rewrite H.
  auto with arith.
Qed.

Theorem addDigit_works_a_little_grittier :
  forall d1 d2 d3 d4 : digit,
    (addDigit d1 d2) = (d3, d4) -> (denoteDigit d1) + (denoteDigit d2) = 10 * (denoteDigit d3) + (denoteDigit d4).
Proof.
  intros.
  rewrite addDigit_works_as_expected.
  unfold denotePair.
  rewrite H.
  reflexivity.
Qed.

Lemma addDigit_bounded : forall (d1 d2 d3 d4 : digit), (d3, d4) = (addDigit d1 d2) -> d3 = D0 \/ d3 = D1.
  intros.
  unfold addDigit in H.
  destruct (lt_dec (denoteDigit d1 + denoteDigit d2) 10).
  left.
  inversion H.
  reflexivity.
  right.
  inversion H.
  reflexivity.
Qed.

Theorem addDigit_assoc_r : forall (d1 d2 d3 : digit),
    (denoteDigit d1) + (denotePair (addDigit d2 d3)) = (denotePair (addDigit d1 d2)) + denoteDigit d3.
Proof.
  intros.
  rewrite <- addDigit_works_as_expected.
  rewrite <- addDigit_works_as_expected.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

Definition addThreeDigits d1 d2 d3 : (digit * digit) :=
  let (rem1, subtotal) := (addDigit d1 d2) in
  let (rem2, total) := (addDigit subtotal d3) in
  let (_, rem) := (addDigit rem1 rem2) in
  (rem, total).

Lemma addThreeDigits_bounded : forall (d1 d2 d3 d4 d5 : digit), (addThreeDigits d1 d2 d3) = (d4, d5) -> denoteDigit d4 <= 2.
Proof.
  intros.
  unfold addThreeDigits in H.
  remember (addDigit d1 d2) as p.
  destruct p as (rem1, subtotal).
  apply (addDigit_bounded d1 d2 rem1 subtotal) in Heqp.
  remember (addDigit subtotal d3) as p.
  destruct p as (rem2, total).
  apply (addDigit_bounded subtotal d3 rem2 total) in Heqp0.
  remember (addDigit rem1 rem2) as p.
  destruct p as (ignored, rem).
  elim Heqp.
  elim Heqp0.
  (* mindless *)
  intros. rewrite H0 in Heqp1. rewrite H1 in Heqp1. inversion Heqp1. inversion H. rewrite <- H5. rewrite H4. auto.
  intros. rewrite H0 in Heqp1. rewrite H1 in Heqp1. inversion Heqp1. inversion H. rewrite <- H5. rewrite H4. auto.
  elim Heqp0.
  intros. rewrite H0 in Heqp1. rewrite H1 in Heqp1. inversion Heqp1. inversion H. rewrite <- H5. rewrite H4. auto.
  intros. rewrite H0 in Heqp1. rewrite H1 in Heqp1. inversion Heqp1. inversion H. rewrite <- H5. rewrite H4. auto.
Qed.

Lemma plus_reg_r : forall (a b c : nat), a + b = c + b <-> a = c.
Proof.
  intros.
  induction b.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  reflexivity.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  split.
  intros.
  apply eq_add_S in H.
  apply IHb in H.
  assumption.
  intros.
  rewrite <- IHb in H.
  apply eq_S in H.
  assumption.
Qed.

Theorem addThreeDigits_works : forall d1 d2 d3, denotePair (addThreeDigits d1 d2 d3) = denoteDigit d1 + denoteDigit d2 + denoteDigit d3.
  intros.
  unfold addThreeDigits.
  remember (addDigit d1 d2) as p1.
  destruct p1 as (rem1, subtotal).
  remember (addDigit subtotal d3) as p2.
  destruct p2 as (rem2, total).
  remember (addDigit rem1 rem2) as p3.
  destruct p3 as (ignored, rem).
  unfold denotePair.
  symmetry in Heqp1.
  rewrite (addDigit_works_a_little_grittier d1 d2 rem1 subtotal Heqp1).
  symmetry in Heqp2.
  rewrite <- plus_assoc.
  rewrite (addDigit_works_a_little_grittier subtotal d3 rem2 total Heqp2).
  rewrite plus_assoc.
  rewrite plus_reg_r.
  symmetry in Heqp1.
  symmetry in Heqp2.

  pose (P := (addDigit_bounded _ _ _ _ Heqp1)).
  pose (Q := (addDigit_bounded _ _ _ _ Heqp2)).

  elim P.
  elim Q.
  intros. rewrite H. rewrite H0. rewrite H in Heqp3. rewrite H0 in Heqp3. inversion Heqp3. auto.
  intros. rewrite H. rewrite H0. rewrite H in Heqp3. rewrite H0 in Heqp3. inversion Heqp3. auto.
  elim Q.
  intros. rewrite H. rewrite H0. rewrite H in Heqp3. rewrite H0 in Heqp3. inversion Heqp3. auto.
  intros. rewrite H. rewrite H0. rewrite H in Heqp3. rewrite H0 in Heqp3. inversion Heqp3. auto.
Qed.

Fixpoint addDigitList_helper_remainder (dl : list digit) (rem : digit) :=
  match dl with
  | [] => [rem]
  | d :: tl =>
    let (rem', x) := addDigit d rem in
    x :: addDigitList_helper_remainder tl rem'
  end.

Fixpoint denoteDigitList_backwards (dl : list digit) : nat :=
  match dl with
  | [] => 0
  | x :: dl => (denoteDigit x) + (10 * denoteDigitList_backwards dl)
  end.

Theorem addDigitList_helper_remainder_works : forall dl rem, denoteDigitList_backwards (addDigitList_helper_remainder dl rem) = denoteDigitList_backwards dl + denoteDigit rem.
Proof.
  induction dl.
  intros.
  unfold denoteDigitList_backwards at 2.
  unfold addDigitList_helper_remainder.
  unfold denoteDigitList_backwards.
  auto.

  intros.
  unfold addDigitList_helper_remainder.
  fold addDigitList_helper_remainder.
  remember (addDigit a rem) as p.
  destruct p as (rem', x).
  unfold denoteDigitList_backwards.
  fold denoteDigitList_backwards.
  rewrite IHdl.
  rewrite Nat.mul_add_distr_l.
  symmetry in Heqp.
  apply addDigit_works_a_little_grittier in Heqp.
  symmetry in Heqp.
  rewrite Nat.add_comm in Heqp.
  Search (_ + (_ + _)).
  rewrite Nat.add_shuffle3.
  rewrite Heqp.
  rewrite Nat.add_comm.
  Search (_ + _ + _).
  rewrite Nat.add_shuffle0.
  reflexivity.
Qed.

Fixpoint addDigitList_helper (dl1 dl2 : list digit) (rem : digit) :=
  match (dl1, dl2) with
  | ([], []) => [rem]
  | ([], _) => addDigitList_helper_remainder dl2 rem
  | (_, []) => addDigitList_helper_remainder dl1 rem
  | (d1 :: tl1, d2 :: tl2) =>
    let (rem', total) := addThreeDigits d1 d2 rem in
    total :: (addDigitList_helper tl1 tl2 rem')
  end.

Definition addDigitList (dl1 : list digit) (dl2 : list digit) :=
  rev (addDigitList_helper (rev dl1) (rev dl2) D0).

Compute (denoteDigitList (addDigitList [ D6; D7 ; D8 ] [ D1; D1; D4 ; D2 ; D3 ])).

Compute (denoteDigitList [ D1 ; D4 ]).

Check fold_right.

Definition denoteDigitListBackwards (dl : list digit) : nat :=
  fold_right (fun d n => (n * 10) + (denoteDigit d)) 0 dl.

Compute (denoteDigitListBackwards [ D1 ; D4 ; D6 ]).

Lemma addDigitList_helper_works :
  forall dl1 dl2 rem dl',
    addDigitList_helper dl1 dl2 rem = denoteDigit rem + denoteDigitListBackwards dl1 + denoteDigitListBackwards dl2.


Theorem addDigitList_works :
  forall dl1 dl2, denoteDigitList dl1 + denoteDigitList dl2 = denoteDigitList (addDigitList dl1 dl2).
  intros.
  unfold addDigitList.




addDigitList_helper dl1 dl2 = dl' ->
