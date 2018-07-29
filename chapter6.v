Require Import PeanoNat NArith.

Definition eq_dec (A:Type) := forall (x y : A), { x = y } + { x <> y }.

Theorem eq_dec_nat : (eq_dec nat).
Proof.
  unfold eq_dec.
  induction x, y.
  left; auto.
  right; apply O_S.
  right; apply Nat.neq_succ_0.
  destruct (IHx y) as [XIsY | XIsNotY].
  left; apply eq_S in XIsY. auto.
  right; apply not_eq_S in XIsNotY. auto.
Qed.

Fixpoint div2 (n : nat) : nat :=
  match n with 0 => 0
          | 1 => 0
          | S (S p) => S (div2 p)
  end.

Theorem div2_le : forall (n:nat), div2 n <= n.
Proof.
  induction n.
  simpl; auto.
  induction n.
  simpl; auto.
Abort.

Theorem div2_le' : forall (n:nat), div2 n <= n.
Proof.
  intros n.
  cut (div2 n <= n /\ div2 (S n) <= (S n)).
  tauto.
  elim n. simpl; auto.
  intros p [H1 H2].
  split; auto.
  simpl; auto with arith.
Qed.

Fixpoint div3 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | 2 => 0
  | S (S (S n)) => S (div3 n)
  end.

Theorem div3_le' : forall (n:nat), div3 n <= n.
Proof.
  intros.
  cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S (S n)) <= (S (S n))).
  tauto.
  elim n.
  simpl; auto.
  intros p [H1 [H2 H3]].
  split; auto.
  split; auto.
  simpl. auto with arith.
Qed.
