(* a ring is a set with various properties
   ring_mult
   ring_add
 *)

Definition is_assoc (A: Set) (f: A -> A -> A) := forall a b c,
  f (f a b) c = f a (f b c).

Definition is_commutative (A: Set) (f: A -> A -> A) := forall a b, f a b = f b a.

Definition has_inverse (A: Set) (f: A -> A -> A) (z: A) := forall a, exists b, f a b = z /\ f b a = z.

Definition is_zero (A: Set) (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

Definition is_semigroup (A: Set) (op: A -> A -> A) (zero: A) := (is_assoc A op) /\ (is_zero A op zero).

Definition is_group (A: Set) (op: A -> A -> A) (zero: A) := is_semigroup A op zero /\ has_inverse A op zero.

Definition is_abelian_group (A: Set) (op: A -> A -> A) (zero: A) := is_group A op zero /\ is_commutative A op.

Section group_laws.

  Variables (A : Set) (op : A -> A -> A) (zero : A).
  Variable (Group : is_group A op zero).

  Lemma inverse: forall (a : A), exists (b : A), op a b = zero /\ op b a = zero.
    unfold is_group, has_inverse in Group.
    destruct Group as [_ HasInverse].
    auto.
  Qed.

  Lemma group_add_l: forall a b c, b = c -> op a b = op a c.
    intros a b c.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma group_add_r: forall a b c, b = c -> op b a = op c a.
    intros a  b c.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma group_zero_r: forall a, op a zero = a.
    destruct Group as [[_ Zero] _]; apply Zero.
  Qed.

  Lemma group_zero_l: forall a, op zero a = a.
    destruct Group as [[_ Zero] _]; apply Zero.
  Qed.

  Lemma group_assoc: forall a b c, op (op a b) c = op a (op b c).
    destruct Group as [[Assoc _] _]; auto.
  Qed.

Lemma group_cancel_l: forall a b c, op a b = op a c -> b = c.
  intros a.
  remember (inverse a) as AInverseExists.
  destruct AInverseExists as [ainverse HAInverse].
  destruct HAInverse as [HAInverse1 HAInverse2].
  intros b c OpABEqOpAC.
  apply (group_add_l ainverse _ _) in OpABEqOpAC.
  rewrite <- group_assoc, <- group_assoc in OpABEqOpAC.
  rewrite HAInverse2 in OpABEqOpAC.
  rewrite group_zero_l, group_zero_l in OpABEqOpAC.
  auto.
Qed.

Lemma group_cancel_r: is_group A op zero -> forall a b c, op b a = op c a -> b = c.
  intros Group a.
  remember (inverse Group a) as AInverseExists.
  destruct AInverseExists as [ainverse HAInverse].
  destruct HAInverse as [HAInverse1 HAInverse2].
  intros b c OpABEqOpAC.
  apply (group_add_r Group ainverse _ _) in OpABEqOpAC.
  rewrite (group_assoc Group), (group_assoc Group) in OpABEqOpAC.
  rewrite HAInverse1 in OpABEqOpAC.
  rewrite (group_zero_r Group), (group_zero_r Group) in OpABEqOpAC.
  auto.
Qed.

Theorem id_is_unique: is_group A op zero -> forall a, (forall b, op a b = b) -> a = zero.
  intros Group.
  intros a.
  intros HA.
  remember (inverse Group a) as HAInverse.
  destruct HAInverse as [a_inverse HAInverse].
  apply (group_cancel_r Group a_inverse).
  rewrite (group_zero_l Group).
  apply (HA a_inverse).
Qed.

(* ring zero *)
(* ring id *)
(* ring mult *)
(* ring add *)
Definition is_ring (A: Set) := A -> A -> (A -> A -> A) -> (A -> A -> A).
