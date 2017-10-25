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

  auto.

  rewrite <- Nat.div_mod.
  auto.
  auto.
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

Definition addDigitToPair d1 p : (digit * digit) :=
  match p with
  | (x, y) =>
    let (rem2, total) := (addDigit y d1) in
    let (_, rem3) := (addDigit rem2 x) in
    (rem3, total)
  end.

Theorem addDigitToPair_works : forall d p,
    denotePair (addDigitToPair d p) = denoteDigit d + denotePair p.
Proof.
  intros.
  unfold addDigitToPair.
  unfold denotePair.
Admitted.

Fixpoint addDigitList_helper_remainder (dl : list digit) (rem : digit) :=
  match dl with
  | [] => [rem]
  | d :: tl =>
    let (rem', x) := addDigit d rem in
    x :: addDigitList_helper_remainder tl rem'
  end.

Fixpoint addDigitList_helper (dl1 dl2 : list digit) (rem : digit) :=
  match (dl1, dl2) with
  | ([], []) => [rem]
  | ([], _) => addDigitList_helper_remainder dl2 rem
  | (_, []) => addDigitList_helper_remainder dl1 rem
  | (d1 :: tl1, d2 :: tl2) =>
    let (rem', total) := addDigitToPair rem (addDigit d1 d2) in
    total :: (addDigitList_helper tl1 tl2 rem')
  end.

Definition addDigitList (dl1 : list digit) (dl2 : list digit) :=
  rev (addDigitList_helper (rev dl1) (rev dl2) D0).

Compute (denoteDigitList (addDigitList [ D6; D7 ; D8 ] [ D1; D1; D4 ; D2 ; D3 ])).

(* this is not correct because condition on rem is incorrect *)
Lemma addDigitList_helper_remainder_works :
  forall dl rem,
    addDigitList_helper_remainder



    Theorem addDigitList_works :
  forall dl1 dl2, denoteDigitList dl1 + denoteDigitList dl2 = denoteDigitList (addDigitList dl1 dl2).
  intros.
