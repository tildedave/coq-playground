Require Import List Arith BinNat.
Import ListNotations.

Inductive digit : Set :=
| Digit : forall n, n < 10 -> digit.

Definition denoteDigit (d : digit) : nat :=
  match d with Digit n _ => n end.

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

Lemma denoteDigit_is_lt_10 : forall (d : digit), denoteDigit d < 10.
Proof.
  intro d; unfold denoteDigit; elim d.
  intros; assumption.
Qed.

Lemma denoteDigit_is_le_9 : forall (d : digit), denoteDigit d <= 9.
Proof.
  intro d.
  assert (denoteDigit d < 10). apply denoteDigit_is_lt_10.
  apply lt_n_Sm_le; assumption.
Qed.

Require Import Omega.

Inductive remainder := R0 | R1.

Definition denotePair p :=
  match p with
  | (R0, d) => (denoteDigit d)
  | (R1, d) => 10 + (denoteDigit d)
  end.

Definition addDigit (d1 : digit) (d2 : digit) : (remainder * digit).
  pose (m := denoteDigit d1).
  pose (n := denoteDigit d2).
  destruct (lt_dec (m + n) 10) as [ TotalLt10 | TotalGt10 ].
  exact (R0, Digit (m + n) TotalLt10).

  assert (m <= 9). apply denoteDigit_is_le_9.
  assert (n <= 9). apply denoteDigit_is_le_9.
  assert (m + n <= 18) as SumMinus20.
  replace 18 with (9 + 9).
  apply plus_le_compat; [ assumption | assumption].
  auto with arith.
  cut (forall a b c, b <= a -> a <= b + c -> a - b <= c).
  intros Cut.
  replace 18 with (9 + 9) in SumMinus20.
  apply Cut in SumMinus20.
  Search (_ <= _ -> _ < _).
  apply le_lt_n_Sm in SumMinus20.
  assert (m + n - 10 < 10) as mPlusNLe10. omega.
  exact (R1, Digit (m + n - 10) mPlusNLe10).
  apply not_lt in TotalGt10; unfold ge in TotalGt10; omega.
  ring.
  intros; omega.
Defined.

Compute (denotePair (addDigit D3 D4)).
Compute (denotePair (addDigit D8 D6)).

Theorem addDigit_works_as_expected :
  forall d1 d2 : digit,
          (denoteDigit d1) + (denoteDigit d2) = (denotePair (addDigit d1 d2)).
Proof.
  intros.
  unfold denotePair, denoteDigit, addDigit.
  destruct (lt_dec (denoteDigit d1 + denoteDigit d2) 10) as [d1_plus_d2_lt_10 | d1_plus_d2_gte_10].
  - auto with arith.
  - apply not_lt in d1_plus_d2_gte_10.
    fold (denoteDigit d1); fold (denoteDigit d2).
    auto with arith.
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

Definition addDigitsWithRemainder (d1 d2 : digit) (r : remainder) : (remainder * digit).
  destruct (addDigit d1 d2) as (r', subtotal).
  case r.
  exact (r', subtotal).
  remember (denoteDigit subtotal) as n.
  destruct (lt_dec (denoteDigit subtotal) 9) as [ SubtotalLt9 | SubtotalEq9 ].
  apply lt_n_S in SubtotalLt9.
  rewrite <- Heqn in SubtotalLt9.
  exact (r', Digit (S n) SubtotalLt9).
  (* this is the situation where d1 + d2 = 9 with one as r, so final answer is 10.
     this means r' = zero by necessity. will need to show this in the theorem *)
  exact (R1, D0).
Defined.

(*Compute (addDigitsWithRemainder D3 D8 R0).*)
Compute (addDigitsWithRemainder D3 D8 R1).
Compute (addDigitsWithRemainder D2 D8 R1).
Compute (addDigitsWithRemainder D1 D8 R1).

Definition denoteRemainder r :=
  match r with
  | R0 => 0
  | R1 => 1
  end.

Lemma denotePair_S : forall r d H, denotePair (r, Digit (S (denoteDigit d)) H) = denotePair (r, d) + 1.
Proof.
  intros r d H.
  unfold denotePair, denoteDigit; destruct d; rewrite Nat.add_1_r.
  destruct r; reflexivity.
Qed.

Lemma addDigit_bounded : forall d1 d2, denotePair (addDigit d1 d2) <= 18.
  intros d1 d2.
  rewrite <- addDigit_works_as_expected.
  remember (denoteDigit_is_le_9 d1).
  remember (denoteDigit_is_le_9 d2).
  omega.
Qed.

Lemma addDigit_R0 : forall d d1 d2, addDigit d1 d2 = (R0, d) -> denoteDigit d1 + denoteDigit d2 = denoteDigit d.
  intros d d1 d2 def_of_d.
  remember (denotePair (addDigit d1 d2)) as n.
  rewrite <- addDigit_works_as_expected in Heqn.
  unfold addDigit in def_of_d.
  destruct (lt_dec (denoteDigit d1 + denoteDigit d2) 10).
  inversion def_of_d.
  unfold denoteDigit.
  auto with arith.
  inversion def_of_d.
Qed.

Theorem addDigitsWithRemainder_works: forall d1 d2 r, denotePair (addDigitsWithRemainder d1 d2 r) = denoteDigit d1 + denoteDigit d2 + denoteRemainder r.
Proof.
  intros d1 d2 r.
  unfold addDigitsWithRemainder.
  remember (addDigit d1 d2) as p.
  destruct p as (r', subtotal).
  destruct r.
  rewrite Heqp, <- addDigit_works_as_expected.
  unfold denoteRemainder; auto with arith.
  destruct (lt_dec (denoteDigit subtotal) 9).
  rewrite denotePair_S.
  rewrite Heqp, <- addDigit_works_as_expected.
  unfold denoteRemainder; auto with arith.
  (* must argue that subtotal = 9.  this is because ~(subtotal < 9), so obviously subtotal = 9 *)
  assert (denoteDigit subtotal = 9) as SubtotalEq9.
  remember (denoteDigit_is_lt_10 subtotal); omega.
  induction r'.
  symmetry in Heqp. apply addDigit_R0 in Heqp.
  rewrite Heqp, SubtotalEq9. compute; auto with arith.
  (* must argue that R1 is impossible because since subtotal = 9, so d1 + d2 can't be 19 *)
  remember (addDigit_bounded d1 d2) as l.
  destruct Heql.
  rewrite <- Heqp in l.
  unfold denotePair in l.
  rewrite SubtotalEq9 in l.
  omega.
Qed.

Lemma plus_reg_r : forall (a b c : nat), a + b = c + b <-> a = c.
Proof.
  intros.
  induction b.
  rewrite Nat.add_0_r, Nat.add_0_r; reflexivity.
  rewrite <- plus_n_Sm, <- plus_n_Sm.
  split.
  intros HSab_eq_Scb.
  apply eq_add_S, IHb in HSab_eq_Scb; assumption.
  intros.
  apply eq_S, IHb; assumption.
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
  rewrite (addDigit_replace d1 d2 rem1 subtotal Heqp1).
  symmetry in Heqp2.
  rewrite <- plus_assoc.
  rewrite (addDigit_replace subtotal d3 rem2 total Heqp2).
  rewrite plus_assoc.
  rewrite plus_reg_r.
  symmetry in Heqp1.
  symmetry in Heqp2.
  destruct (addDigit_bounded _ _ _ _ Heqp1, addDigit_bounded _ _ _ _ Heqp2)
    as [[rem1_D0 | rem1_D1] [rem2_D0 | rem2_D1]].
  - intros; rewrite rem1_D0, rem2_D0. rewrite rem1_D0, rem2_D0 in Heqp3.
    inversion Heqp3; auto.
  - intros; rewrite rem1_D0, rem2_D1. rewrite rem1_D0, rem2_D1 in Heqp3.
    inversion Heqp3; auto.
  - intros; rewrite rem1_D1, rem2_D0. rewrite rem1_D1, rem2_D0 in Heqp3.
    inversion Heqp3; auto.
  - intros; rewrite rem1_D1, rem2_D1. rewrite rem1_D1, rem2_D1 in Heqp3.
    inversion Heqp3; auto.
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
  apply addDigit_replace in Heqp.
  symmetry in Heqp.
  rewrite Nat.add_comm in Heqp.
  rewrite Nat.add_shuffle3.
  rewrite Heqp.
  ring.
Qed.

Fixpoint addDigitList_helper (dl1 dl2 : list digit) (rem : digit) :=
  match (dl1, dl2) with
  | ([], []) => [rem]
  | ([], _) => addDigitList_helper_remainder dl2 rem
  | (_, []) => addDigitList_helper_remainder dl1 rem
  | (d1 :: tl1, d2 :: tl2) =>
    let (rem', total) := addDigitsWithRemainder d1 d2 rem in
    total :: (addDigitList_helper tl1 tl2 rem')
  end.

Lemma list_cons_app : forall (A : Type) (a : A) (l : (list A)), a :: l = [a] ++ l.
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma denoteDigitList_backwards_single : forall d, denoteDigitList_backwards [d] = denoteDigit d.
Proof.
  intros.
  unfold denoteDigitList_backwards.
  rewrite <- mult_n_O, <- plus_n_O; reflexivity.
Qed.

Lemma denoteDigitList_backwards_empty : denoteDigitList_backwards [] = 0.
Proof.
  intros.
  unfold denoteDigitList_backwards; reflexivity.
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
  (* playing with the terms so they end up with the right terms on LHS/RHS
     annoying, feels like this should be easier *)
  replace (denoteDigit total +
           10 * (denoteDigit rem' +
                 denoteDigitList_backwards dl1 +
                 denoteDigitList_backwards dl2))
    with (denoteDigit total +
          10 * denoteDigit rem' +
          10 * denoteDigitList_backwards dl1 +
          10 * denoteDigitList_backwards dl2).
  replace (denoteDigit rem +
           (denoteDigit a + 10 * denoteDigitList_backwards dl1) +
           (denoteDigit d + 10 * denoteDigitList_backwards dl2))
    with (denoteDigit rem +
          denoteDigit a +
          denoteDigit d +
          10 * denoteDigitList_backwards dl1 +
          10 * denoteDigitList_backwards dl2).
  rewrite plus_reg_r, plus_reg_r.
  rewrite plus_comm.
  fold (denotePair (rem', total)).
  rewrite Heqp, addThreeDigits_works; ring.
  ring.
  ring.
Qed.

Definition addDigitList (dl1 : list digit) (dl2 : list digit) :=
  rev (addDigitList_helper (rev dl1) (rev dl2) D0).

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

Lemma denoteDigitList_backwards_app : forall dl1 dl2,
    denoteDigitList_backwards (dl1 ++ dl2) = 10 ^ (length dl1) * denoteDigitList_backwards dl2 + denoteDigitList_backwards dl1.
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
  rewrite IHdl1, Nat.mul_add_distr_l, Nat.mul_assoc, <- Nat.pow_succ_r.
  (* need to drop the denoteDigitList_backwards dl2 term from both sides *)
  replace (10 ^ S (length dl1)) with (10 ^ (length (a :: dl1))).
  rewrite plus_comm, <- plus_assoc, Nat.add_cancel_l.
  symmetry.
  unfold denoteDigitList_backwards.
  fold denoteDigitList_backwards.
  ring.
  auto with arith.
  apply length_always_gte_0.
Qed.

Lemma denoteDigitList_backwards_rev_cons : forall dl a, denoteDigitList_backwards (rev (a :: dl)) = 10 ^ (length dl) * (denoteDigit a) + denoteDigitList_backwards (rev dl).
Proof.
  induction dl.
  intro a0; simpl; ring.
  intro a0.
  rewrite list_cons_app, rev_app_distr.
  unfold rev at 2.
  rewrite app_nil_l, denoteDigitList_backwards_app, IHdl, rev_length, Nat.add_cancel_r.
  unfold denoteDigitList_backwards.
  ring.
Qed.

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
  intros; unfold denoteDigitList_helper; simpl; ring.
  intros m n.
  rewrite denoteDigitList_helper_cons, Nat.mul_add_distr_l.
  rewrite <- plus_assoc, IHdl, Nat.mul_add_distr_r.
  replace (n * 10 ^ length (a :: dl)) with (10 * n * 10 ^ length dl).
  rewrite plus_comm.
  symmetry.
  rewrite plus_comm, <- plus_assoc, Nat.add_cancel_l, denoteDigitList_helper_cons.
  symmetry.
  rewrite IHdl.
  ring.
  (* previous form was more convenient to show correctness, now we rewrite
     again *)
  replace (10 * n * 10 ^ length dl)
    with ((10 * 10 ^ length dl) * n) ; [auto | ring].
  rewrite <- Nat.pow_succ_r ; [auto | apply length_always_gte_0].
  replace (length (a :: dl)) with (S (length dl)); [ring | auto].
Qed.

Lemma denoteDigitList_helper_cons_unwrap : forall dl a acc, denoteDigitList_helper (a :: dl) acc = 10 ^ length dl * denoteDigit a + denoteDigitList_helper dl (acc * 10).
Proof.
  induction dl.
  intros a acc.
  rewrite denoteDigitList_helper_cons.
  unfold denoteDigitList_helper.
  symmetry.
  unfold length; rewrite Nat.pow_0_r; ring.

  intros a0 acc.
  (* don't want to unfold both a0 :: a so we use a temp variable *)
  remember (a :: dl) as dl'.
  rewrite denoteDigitList_helper_cons, Heqdl', denoteDigitList_helper_split, plus_comm.
  replace (10 * acc) with (acc * 10); [rewrite Nat.add_cancel_r ; ring | ring].
Qed.

Lemma denoteDigitList_unwrap : forall dl a, denoteDigitList (a :: dl) = 10 ^ length dl * denoteDigit a + denoteDigitList dl.
Proof.
  induction dl.
  intros.
  unfold denoteDigitList, denoteDigitList_helper; simpl; ring.

  intros.
  unfold denoteDigitList.
  rewrite denoteDigitList_helper_cons_unwrap, Nat.add_cancel_l.
  simpl; reflexivity.
Qed.

Lemma denoteDigitList_backwards_rev : forall dl, denoteDigitList_backwards (rev dl) = denoteDigitList dl.
Proof.
  induction dl.
  intros; compute; reflexivity.

  rewrite denoteDigitList_backwards_rev_cons.
  rewrite IHdl.
  symmetry.
  rewrite denoteDigitList_unwrap; reflexivity.
Qed.

Lemma denoteDigitList_app : forall dl1 dl2, denoteDigitList (dl1 ++ dl2) = 10 ^ (length dl2) * denoteDigitList dl1 + denoteDigitList dl2.
Proof.
  induction dl1.
  intros.
  rewrite app_nil_l.
  symmetry.
  unfold denoteDigitList at 1.
  unfold denoteDigitList_helper.
  ring.

  intros.
  rewrite <- app_comm_cons.
  unfold denoteDigitList.
  rewrite denoteDigitList_helper_cons_unwrap.
  symmetry.
  rewrite denoteDigitList_helper_cons_unwrap.
  simpl.
  fold (denoteDigitList dl1).
  fold (denoteDigitList dl2).
  fold (denoteDigitList (dl1 ++ dl2)).
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_assoc.

  replace (10 ^ length dl2 * 10 ^ length dl1) with (10 ^ length (dl1 ++ dl2)).
  rewrite <- Nat.add_assoc.
  rewrite Nat.add_cancel_l.
  symmetry.
  rewrite IHdl1.
  reflexivity.

  (* proof of replacement *)
  rewrite <- Nat.pow_add_r, plus_comm.
  rewrite app_length.
  reflexivity.
Qed.

Lemma denoteDigitList_rev : forall dl, denoteDigitList (rev dl) = denoteDigitList_backwards dl.
Proof.
  induction dl.
  compute.
  reflexivity.

  rewrite list_cons_app, rev_app_distr.
  unfold rev at 2.
  rewrite app_nil_l, denoteDigitList_app.
  unfold length, denoteDigitList at 2, denoteDigitList_helper.
  rewrite Nat.mul_0_l, Nat.pow_1_r, Nat.add_0_l.
  rewrite denoteDigitList_backwards_app.
  unfold length.
  rewrite Nat.pow_1_r.
  rewrite <- IHdl.
  rewrite Nat.add_cancel_l.
  unfold denoteDigitList_backwards.
  ring.
Qed.

Theorem addDigitList_works :
  forall dl1 dl2, denoteDigitList dl1 + denoteDigitList dl2 = denoteDigitList (addDigitList dl1 dl2).
Proof.
  intros.
  unfold addDigitList.
  symmetry.
  rewrite denoteDigitList_rev, addDigitList_helper_works, denoteDigitList_backwards_rev, denoteDigitList_backwards_rev, Nat.add_cancel_r.
  unfold denoteDigit.
  simpl.
  reflexivity.
Qed.

Lemma mod_is_lt : forall (m n : nat), n > 0 -> (m mod n) < n.
  intros.
  apply (Nat.mod_bound_pos m n (all_nat_gte_zero m)).
  exact H.
Qed.

Lemma TenGt0 : 10 > 0.
Proof.
  auto with arith.
Qed.

(* https://stackoverflow.com/questions/33302526/well-founded-recursion-in-coq *)
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Fixpoint convertToDigitList_helper (n i : nat) : (list digit) :=
  match i with
  | 0 => []
  | (S p) =>
    let a := n mod 10 in
    let m := n / 10 in
    let d := Digit a (mod_is_lt n 10 TenGt0) in
    if eq_nat_dec m 0 then
      [d]
    else
      (convertToDigitList_helper m p) ++ [d]
  end.

Definition convertToDigitList (n : nat) : (list digit) :=
  convertToDigitList_helper n n.

Compute (convertToDigitList 123).

Lemma div_zero_implies_small : (forall a b, b <> 0 -> a / b = 0 -> a < b).
Proof.
  intros a b b_neq_0 a_div_b_eq_0.
  apply (Nat.div_str_pos_iff a b) in b_neq_0.
  omega.
Qed.


Lemma div_nonzero_implies_not_small : (forall a b, b <> 0 -> a / b <> 0 -> b <= a).
  intros a b b_neq_0.
  apply (Nat.div_str_pos_iff a b) in b_neq_0.
  intros a_b_neq_0.
  omega.
Qed.

Lemma denoteDigitList_trivial : forall d : digit, denoteDigitList [d] = denoteDigit d.
Proof.
  intro d.
  unfold denoteDigitList.
  unfold denoteDigitList_helper.
  ring.
Qed.

Require Import Arith Wf.

Lemma convertToDigitList_helper_works :
  forall m i, m <= i -> denoteDigitList (convertToDigitList_helper m i) = m.
Proof.
  induction m as [ m IHn ] using (well_founded_induction lt_wf).
  intros i m_bounded.
  unfold convertToDigitList_helper.
  destruct i.
  compute; omega.

  fold convertToDigitList_helper.
  destruct (Nat.eq_dec (m / 10) 0) as [m_div_10_eq_0 | m_div_10_neq_0].
  apply div_zero_implies_small in m_div_10_eq_0 ; [auto | auto].
  apply Nat.mod_small in m_div_10_eq_0; auto.
  cut (m / 10 < m).
  intros m_lt_10_lt_m.
  Search (denoteDigitList (_ ++ _)).
  rewrite denoteDigitList_app.
  rewrite IHn.
  unfold length.
  rewrite denoteDigitList_trivial.
  unfold denoteDigit.
  rewrite Nat.pow_1_r.
  symmetry.
  apply Nat.div_mod; [auto].
  omega.
  omega.
  apply Nat.div_lt; [auto|auto with arith].
  apply div_nonzero_implies_not_small; [auto | auto].
  rewrite Nat.div_1_r.
  unfold not.
  intros Hm_0.
  rewrite Hm_0 in m_div_10_neq_0.
  auto.
Qed.

Theorem convertToDigitList_works : forall n : nat, denoteDigitList (convertToDigitList n) = n.
Proof.
  intros n.
  unfold convertToDigitList.
  apply convertToDigitList_helper_works ; auto.
Qed.

Compute (convertToDigitList 123).

Theorem grade_school_addition_correct: forall m n, denoteDigitList (addDigitList (convertToDigitList m) (convertToDigitList n)) = m + n.
Proof.
  intros m n.
  rewrite <- addDigitList_works.
  repeat rewrite convertToDigitList_works.
  reflexivity.
Qed.

Recursive Extraction addDigitList convertToDigitList.

  (* Multiplication *)

(* 123 * 456 = (100 + 20 + 3) * (400 + 50 + 6) *)
(* 100 * 400 + 100 * 50 + 100 * 6 + 20 * 400 + 20 * 50 + 20 * 6 + 3 * 400 + 3 * 50 + 3 * 6 *)

Fixpoint multiplyDigit (d1 : digit) (d2 : digit) : (digit * digit).
  pose (m := denoteDigit d1).
  pose (n := denoteDigit d2).
  destruct (lt_dec (m * n) 10) as [ TotalLt10 | TotalGt10 ].
  exact (D0, Digit (m * n) TotalLt10).

  (* Must prove that multiplying two digits gives a remainder / modulus both < 10 *)
  assert (m * n <= 81) as MultBounded.
  Search (_ <= _ -> _ < _).
  assert (m <= 9). apply denoteDigit_is_le_9.
  assert (n <= 9). apply denoteDigit_is_le_9.
  apply (mult_le_compat _ _ _ _ H H0).

  pose (a := (m * n) / 10).
  pose (b := (m * n) mod 10).

  assert (b < 10) as ModLt10. apply mod_is_lt. auto with arith.
  assert (a < 10) as RemainderLt10.
  Search (_ <= _ -> _ / _ <= _).
  apply (Nat.div_le_mono (m * n) 81 10) in MultBounded.
  assert (81 / 10 = 8). auto with arith.
  rewrite H in MultBounded.
  apply le_lt_n_Sm in MultBounded.
  apply Nat.lt_lt_succ_r in MultBounded.
  exact MultBounded.
  auto with arith.
  exact (Digit a RemainderLt10, Digit b ModLt10).
Defined.

Fixpoint multiplyDigitList_backwards_helper (dl : list digit) (d : digit) : list digit :=
  match dl with
  | [] => []
  | d' :: dl =>
    let (rem, d0) := (multiplyDigit d d') in
    let dl' := (multiplyDigitList_backwards_helper dl d) in
    d0 :: (addDigitList_helper dl' [rem] D0)
  end.
