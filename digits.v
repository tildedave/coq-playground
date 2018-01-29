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

Fixpoint denoteDigitList_helper (dl : list digit) (acc : nat) :=
  match dl with
  | [] => acc
  | a :: dl => denoteDigitList_helper dl ((acc * 10) + (denoteDigit a))
  end.

(* using explicit recursion over fold_left because I can't figure out how re-"fold" the induction for induction proofs *)
Definition denoteDigitList dl := denoteDigitList_helper dl 0.

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

(* Not sure why I need this, I imagine there is some way to just "fold" the RHS into a denotePair *)
Lemma denotePair_rewrite : forall d1 d2, denotePair (d1, d2) = 10 * denoteDigit d1 + denoteDigit d2.
Proof.
  intros.
  unfold denotePair.
  reflexivity.
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

Search (_ ++ _).

Lemma list_cons_app : forall (A : Type) (a : A) (l : (list A)), a :: l = [a] ++ l.
Proof.
  induction l.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

Lemma denoteDigitList_backwards_single : forall d, denoteDigitList_backwards [d] = denoteDigit d.
Proof.
  intros.
  unfold denoteDigitList_backwards.
  Search (_ * 0).
  rewrite <- mult_n_O.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma denoteDigitList_backwards_empty : denoteDigitList_backwards [] = 0.
Proof.
  intros.
  unfold denoteDigitList_backwards.
  compute.
  reflexivity.
Qed.

Lemma addDigitList_helper_works :
  forall dl1 dl2 rem,
    denoteDigitList_backwards (addDigitList_helper dl1 dl2 rem) = denoteDigit rem + denoteDigitList_backwards dl1 + denoteDigitList_backwards dl2.
Proof.
  induction dl1.
  induction dl2.
  intros.
  unfold addDigitList_helper.
  rewrite denoteDigitList_backwards_single.
  rewrite denoteDigitList_backwards_empty.
  ring.

  intros.
  unfold addDigitList_helper.
  rewrite addDigitList_helper_remainder_works.
  rewrite denoteDigitList_backwards_empty.
  ring.

  intros.
  destruct dl2.
  unfold addDigitList_helper at 1.
  rewrite addDigitList_helper_remainder_works.
  rewrite denoteDigitList_backwards_empty.
  ring.

  unfold addDigitList_helper.
  remember (addThreeDigits a d rem) as p.
  destruct p as (rem', total).
  fold addDigitList_helper.
  unfold denoteDigitList_backwards at 1.
  fold denoteDigitList_backwards.
  rewrite IHdl1.
  unfold denoteDigitList_backwards at 3.
  unfold denoteDigitList_backwards at 3.
  fold denoteDigitList_backwards.
  fold denoteDigitList_backwards.
  (* playing with the terms so they end up with the right terms on LHS/RHS annoying, feels like this should be easier *)
  assert (denoteDigit total + 10 * (denoteDigit rem' + denoteDigitList_backwards dl1 + denoteDigitList_backwards dl2) = denoteDigit total + 10 * denoteDigit rem' + 10 * denoteDigitList_backwards dl1 + 10 * denoteDigitList_backwards dl2).
  ring.
  rewrite H.
  assert (denoteDigit rem + (denoteDigit a + 10 * denoteDigitList_backwards dl1) + (denoteDigit d + 10 * denoteDigitList_backwards dl2) = (denoteDigit rem + denoteDigit a + denoteDigit d + 10 * denoteDigitList_backwards dl1 + 10 * denoteDigitList_backwards dl2)).
  ring.
  rewrite H0.
  rewrite plus_reg_r.
  rewrite plus_reg_r.
  destruct H. (* don't need this *)
  destruct H0. (* don't need this *)
  rewrite plus_comm.
  rewrite <- denotePair_rewrite.
  rewrite Heqp.
  rewrite addThreeDigits_works.
  ring.
Qed.

Definition addDigitList (dl1 : list digit) (dl2 : list digit) :=
  rev (addDigitList_helper (rev dl1) (rev dl2) D0).

Compute (denoteDigitList_backwards (rev [ D6 ; D7 ; D8 ])).
Compute (denoteDigitList [ D6 ; D7 ; D8 ]).


Lemma wtf2 : forall (A : Type) (l : list A) m, (length l) = (S m) <-> exists a x, l = a :: x.
Proof.
  intros.
  split.
  intros.
  unfold length in H.
  (* feels like this should be easy *)
Admitted.

Compute denoteDigitList_backwards [ D1 ; D2 ; D3 ].
Compute (10 ^1 * (denoteDigitList_backwards [D2 ; D3])) + (denoteDigitList_backwards [D1]).

Lemma length_always_gte_0 : forall (A : Type) (l : list A), length l >= 0.
Proof.
  intros.
  induction l.
  unfold length.
  auto.
  rewrite list_cons_app.
  rewrite app_length.
  unfold length at 1.
  auto.
Qed.

Lemma denoteDigitList_backwards_split : forall dl1 dl2, denoteDigitList_backwards (dl1 ++ dl2) = 10 ^ (length dl1) * denoteDigitList_backwards dl2 + denoteDigitList_backwards dl1.
Proof.
  induction dl1.
  intros.
  rewrite app_nil_l.
  symmetry.
  unfold length.
  rewrite Nat.pow_0_r.
  unfold denoteDigitList_backwards at 2.
  ring.

  intros.
  rewrite <- app_comm_cons.
  unfold denoteDigitList_backwards at 1.
  fold denoteDigitList_backwards.
  rewrite IHdl1.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_assoc.
  rewrite <- Nat.pow_succ_r.
  (* need to drop the denoteDigitList_backwards dl2 term from both sides *)
  assert (10 ^ S (length dl1) = 10 ^ (length (a :: dl1))).
  auto.
  rewrite H.
  rewrite plus_comm.
  rewrite <- plus_assoc.
  rewrite Nat.add_cancel_l.
  symmetry.
  unfold denoteDigitList_backwards.
  fold denoteDigitList_backwards.
  ring.

  apply length_always_gte_0.
Qed.

Lemma denoteDigitList_backwards_rev_cons : forall dl a, denoteDigitList_backwards (rev (a :: dl)) = 10 ^ (length dl) * (denoteDigit a) + denoteDigitList_backwards (rev dl).
Proof.
  induction dl.
  intro a0.
  simpl.
  ring.

  intro a0.
  rewrite list_cons_app.
  rewrite rev_app_distr.
  unfold rev at 2.
  rewrite app_nil_l.
  rewrite denoteDigitList_backwards_split.
  rewrite IHdl.
  Search (length (rev _)).
  rewrite rev_length.
  rewrite Nat.add_cancel_r.
  unfold denoteDigitList_backwards.
  ring.
Qed.

(* I don't think I need this, needed this for denoteDigitList_backwards because of the presence of 'rev' *)
Lemma denoteDigitList_split : forall dl1 dl2, denoteDigitList (dl1 ++ dl2) = 10 ^ (length dl2) * denoteDigitList dl1 + denoteDigitList dl2.
Proof.
  induction dl1.
  intros.
  rewrite app_nil_l.
  symmetry.
  unfold denoteDigitList at 1.
  unfold denoteDigitList_helper.
  ring.

  intros.
  Search ((_ :: _) ++ _).
  rewrite <- app_comm_cons.
  unfold denoteDigitList at 1.
Abort.

Lemma denoteDigitList_helper_cons : forall dl a acc, denoteDigitList_helper (a :: dl) acc = denoteDigitList_helper dl (10 * acc + denoteDigit a).
Proof.
  intros.
  unfold denoteDigitList_helper at 1.
  fold denoteDigitList_helper.
  rewrite mult_comm.
  reflexivity.
Qed.

Lemma denoteDigitList_helper_split : forall dl m n, denoteDigitList_helper dl (m + n) = denoteDigitList_helper dl m + n * 10 ^ (length dl).
Proof.
  induction dl.
  intros.
  unfold denoteDigitList_helper.
  simpl.
  ring.

  intros.
  rewrite denoteDigitList_helper_cons.
  Search (_ * (_ + _)).
  rewrite Nat.mul_add_distr_l.
  rewrite <- plus_assoc.
  rewrite IHdl.
  Search (_ * _).
  rewrite Nat.mul_add_distr_r.
  assert (n * 10 ^ length (a :: dl) = 10 * n * 10 ^ length dl).
  unfold length.
  rewrite Nat.pow_succ_r.
  rewrite Nat.mul_comm.
  symmetry.
  Search (_ * _ * _).
  rewrite Nat.mul_shuffle0.
  reflexivity.
  fold (length dl).
  apply length_always_gte_0.
  rewrite H.
  rewrite plus_comm.
  symmetry.
  rewrite plus_comm.
  symmetry.
  rewrite <- plus_assoc.
  rewrite Nat.add_cancel_l.
  rewrite denoteDigitList_helper_cons.
  symmetry.
  rewrite IHdl.
  ring.
Qed.

Lemma denoteDigitList_helper_cons_unwrap : forall dl a acc, denoteDigitList_helper (a :: dl) acc = 10 ^ length dl * denoteDigit a + denoteDigitList_helper dl (acc * 10).
Proof.
  induction dl.
  intros.
  rewrite denoteDigitList_helper_cons.
  unfold denoteDigitList_helper.
  symmetry.
  unfold length.
  rewrite Nat.pow_0_r.
  ring.

  (* So I do need to prove this :) *)

  intros.
  (* don't want to unfold both a0 :: a so we use a temp variable *)
  remember (a :: dl) as dl'.
  rewrite denoteDigitList_helper_cons.
  rewrite Heqdl'.
  rewrite denoteDigitList_helper_split.
  rewrite plus_comm.
  assert (10 * acc = acc * 10).
  ring.
  rewrite H.
  rewrite Nat.add_cancel_r.
  ring.
Qed.

Lemma denoteDigitList_unwrap : forall dl a, denoteDigitList (a :: dl) = 10 ^ length dl * denoteDigit a + denoteDigitList dl.
Proof.
  induction dl.
  intros.
  unfold denoteDigitList.
  unfold denoteDigitList_helper.
  simpl.
  ring.

  intros.
  unfold denoteDigitList.
  rewrite denoteDigitList_helper_cons_unwrap.
  rewrite Nat.add_cancel_l.
  simpl.
  reflexivity.
Qed.

Lemma denoteDigitList_backwards_rev : forall dl, denoteDigitList_backwards (rev dl) = denoteDigitList dl.
Proof.
  induction dl.
  intros.
  compute.
  reflexivity.

  rewrite denoteDigitList_backwards_rev_cons.
  rewrite IHdl.
  symmetry.
  rewrite denoteDigitList_unwrap.
  ring.
Qed.

Compute (denoteDigitList (addDigitList [ D6; D7 ; D8 ] [ D1; D1; D4 ; D2 ; D3 ])).

Compute (denoteDigitList [ D1 ; D4 ]).

Lemma denoteDigitList_rev1 : forall dl, denoteDigitList (rev dl) = denoteDigitList_backwards dl.
Proof.
  induction dl.
  intros.
  unfold rev.
  unfold denoteDigitList.
  unfold denoteDigitList_backwards.
  compute.
  reflexivity.

  (* induction case is a pain, come back to this later *)
Admitted.

Theorem addDigitList_works :
  forall dl1 dl2, denoteDigitList dl1 + denoteDigitList dl2 = denoteDigitList (addDigitList dl1 dl2).
  intros.
  unfold addDigitList.




addDigitList_helper dl1 dl2 = dl' ->
