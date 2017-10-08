Require Import List Arith BinNat.
Import ListNotations.

Inductive digit : Set :=
| Digit : forall n, n >= 0 -> n < 10 -> digit.

Fixpoint denoteDigit (d : digit) : nat :=
  match d with Digit n _ _ => n end.

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

Definition denoteDigitList (dl : list digit) : nat :=
  fold_left (fun n d => (n * 10) + (denoteDigit d)) dl 0.

Compute (denoteDigitList [D3 ; D4 ; D7]).

Definition toDigit (n : nat | n >= 0 /\ n < 10) : digit.
  inversion n.
  elim H.
  intros.
  exact (Digit x H0 H1).
Defined.

Lemma mod_is_lt : forall (m n : nat), (m mod n) < n.
  intros.
Admitted.

Lemma div_is_lt : forall (m n : nat), (m / n) < n.
  intros.
Admitted.

Lemma all_nat_gt_zero : forall m, m >= 0.
  intros.
  induction m.
  auto.
  auto with arith.
Qed.

Check (mod_is_lt (2 + 10) 3).

Definition addDigit (d1 : digit) (d2 : digit) : (option digit * digit).
  pose (m := denoteDigit d1).
  pose (n := denoteDigit d2).
  remember ((m + n) mod 10) as total.
  remember ((m + n) / 10) as remainder.
  assert (total < 10) as TotalLt10. rewrite Heqtotal. apply mod_is_lt.
  assert (remainder < 10) as RemainderLt10. rewrite Heqremainder. apply div_is_lt.
  destruct (beq_nat remainder 0).
  exact (None, Digit total (all_nat_gt_zero total) TotalLt10).
  exact (Some (Digit remainder (all_nat_gt_zero remainder) RemainderLt10),
         Digit total (all_nat_gt_zero total) TotalLt10).
Defined.

Compute (addDigit D7 D6).