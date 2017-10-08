Require Import List Arith BinNat.
Import ListNotations.

Inductive digit : Set :=
| Digit : forall n, n >= 0 -> n < 10 -> digit.

Fixpoint denoteDigit (d : digit) : nat :=
  match d with Digit n _ _ => n end.

Definition denotePair p :=
  match p with
    (d1, d2) => 10 * (denoteDigit d1) + (denoteDigit d2)
  end.

Definition denoteDigitList (dl : list digit) : nat :=
  fold_left (fun n d => (n * 10) + (denoteDigit d)) dl 0.

Definition D0 : digit.
  refine (Digit 0 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D1 : digit.
  refine (Digit 1 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D2 : digit.
  refine (Digit 2 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D3 : digit.
  refine (Digit 3 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D4 : digit.
  refine (Digit 4 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D5 : digit.
  refine (Digit 5 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D6 : digit.
  refine (Digit 6 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D7 : digit.
  refine (Digit 7 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D8 : digit.
  refine (Digit 8 _ _).
  auto with arith.  auto with arith.
Defined.

Definition D9 : digit.
  refine (Digit 9 _ _).
  auto with arith.  auto with arith.
Defined.

Compute (denoteDigitList [D3 ; D4 ; D7]).

Definition toDigit (n : nat | n >= 0 /\ n < 10) : digit.
  inversion n.
  elim H.
  intros.
  exact (Digit x H0 H1).
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

Lemma div_is_lt : forall (m n : nat), (m / n) < n.
  intros.
Admitted.

Check (mod_is_lt (2 + 10) 3).

Definition addDigit (d1 : digit) (d2 : digit) : (digit * digit).
  pose (m := denoteDigit d1).
  pose (n := denoteDigit d2).
  remember ((m + n) mod 10) as total.
  remember ((m + n) / 10) as remainder.
  assert (total < 10) as TotalLt10. rewrite Heqtotal. apply mod_is_lt. auto with arith.
  assert (remainder < 10) as RemainderLt10. rewrite Heqremainder. apply div_is_lt.
  exact (Digit remainder (all_nat_gte_zero remainder) RemainderLt10,
         Digit total (all_nat_gte_zero total) TotalLt10).
Defined.

Theorem addDigit_works_as_expected :
  forall d1 d2 : digit,
    (denoteDigit d1) + (denoteDigit d2) = (denotePair (addDigit d1 d2)).
Proof.
  intros.
  unfold denotePair.
  unfold denoteDigit.
  unfold addDigit.
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
  destruct p.
Admitted.

Fixpoint addDigitList_helper (dl1 dl2 : list digit) (rem : digit) :=
  match (dl1, dl2) with
  | ([], _) => rem :: dl2
  | (_, []) => rem :: dl1
  | (d1 :: tl1, d2 :: tl2) =>
    let (rem', total) := addDigitToPair rem (addDigit d1 d2) in
    total :: (addDigitList_helper tl1 tl2 rem')
  end.

Definition addDigitList (dl1 : list digit) (dl2 : list digit) :=
  rev (addDigitList_helper (rev dl1) (rev dl2) D0).

Compute addDigitList [ D6; D7 ; D8 ] [ D4 ; D2 ; D3 ].