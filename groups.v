(* a ring is a set with various properties
   ring_mult
   ring_add
 *)

Section group_definitions.
  Definition is_assoc (A: Set) (f: A -> A -> A) := forall a b c,
    f (f a b) c = f a (f b c).

  Definition is_commutative (A: Set) (f: A -> A -> A) := forall a b, f a b = f b a.

  Definition has_inverse (A: Set) (f: A -> A -> A) (z: A) := forall a, exists b, f a b = z /\ f b a = z.

  Definition is_zero (A: Set) (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

  Definition is_semigroup (A: Set) (op: A -> A -> A) (zero: A) := (is_assoc A op) /\ (is_zero A op zero).

  Definition is_group (A: Set) (op: A -> A -> A) (zero: A) := is_semigroup A op zero /\ has_inverse A op zero.

  Definition is_abelian_group (A: Set) (op: A -> A -> A) (zero: A) := is_group A op zero /\ is_commutative A op.

End group_definitions.

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
    repeat rewrite <- group_assoc in OpABEqOpAC.
    rewrite HAInverse2 in OpABEqOpAC.
    repeat rewrite group_zero_l in OpABEqOpAC.
    auto.
  Qed.

  Lemma group_cancel_r: forall a b c, op b a = op c a -> b = c.
    intros a.
    remember (inverse a) as AInverseExists.
    destruct AInverseExists as [ainverse HAInverse].
    destruct HAInverse as [HAInverse1 HAInverse2].
    intros b c OpABEqOpAC.
    apply (group_add_r ainverse _ _) in OpABEqOpAC.
    repeat rewrite group_assoc in OpABEqOpAC.
    rewrite HAInverse1 in OpABEqOpAC.
    repeat rewrite group_zero_r in OpABEqOpAC.
    auto.
  Qed.

  Theorem id_is_unique: forall a, (forall b, op a b = b) -> a = zero.
    intros a HA.
    remember (inverse a) as HAInverse.
    destruct HAInverse as [a_inverse HAInverse].
    apply (group_cancel_r a_inverse).
    rewrite group_zero_l.
    apply (HA a_inverse).
  Qed.

  Theorem inverse_commutes: forall a b, op a b = zero <-> op b a = zero.
    intros a b.
    split.
    intro OpABZero.
    symmetry.
    apply (group_cancel_l a _ _), (group_cancel_l b _ _).
    rewrite <- group_assoc, <- (group_assoc a b a).
    rewrite OpABZero, group_zero_r, group_zero_l.
    reflexivity.
    intro OpBAZero.
    symmetry.
    apply (group_cancel_l b _ _), (group_cancel_l a _ _).
    rewrite <- group_assoc, <- (group_assoc b a b).
    rewrite OpBAZero, group_zero_r, group_zero_l.
    reflexivity.
  Qed.

  Theorem inverse_unique: forall a b c, op a b = zero /\ op a c = zero -> b = c.
    intros a b c.
    intros [H1 H2].
    apply (group_cancel_l a _ _).
    rewrite H1, H2; reflexivity.
  Qed.
End group_laws.

Section subgroups.

  Variables (A : Set) (op : A -> A -> A) (zero : A).
  Variable (Group : is_group A op zero).

  (* subgroup_mem is a characteristic function.  not sure if it will need to
     be A -> Prop instead of a -> bool. *)
  Definition is_subgroup (subgroup_mem: A -> bool) :=
    (* 0 is a subgroup member *)
    subgroup_mem zero = true /\
    (* subgroup is closed under operation *)
    (forall a b, subgroup_mem a = true /\ subgroup_mem b = true ->
                 subgroup_mem (op a b) = true) /\
    (* if an element is in the subgroup, its inverse is too *)
    (forall a, subgroup_mem a = true ->
               exists b, subgroup_mem b = true /\ op a b = zero).

  Definition left_coset (a: A) (subgroup_mem: A -> bool) (coset_mem: A -> bool) :=
    is_subgroup subgroup_mem /\
    forall (b: A), subgroup_mem b = true <-> coset_mem (op a b) = true.

  Definition right_coset (a: A) (subgroup_mem: A -> bool) (coset_mem: A -> bool) :=
    is_subgroup subgroup_mem /\
    forall (c: A), coset_mem c = true <->
                   exists b, subgroup_mem b = true /\ (op b a)  = c.

  Lemma subgroup_op_closed: forall a b H,
      is_subgroup H -> H a = true -> H b = true -> H (op a b) = true.
  Proof.
    intros a b H.
    unfold is_subgroup.
    intros [_ [H_closed _]].
    intros Ha Hb.
    apply H_closed.
    auto.
  Qed.

  (* a in Hb -> Ha = Hb *)
  Lemma coset_intersection_helper:
    forall a b H Ha Hb,
      right_coset a H Ha /\ right_coset b H Hb ->
      (exists x, (Ha x = true /\ Hb x = true)) ->
                (forall c, Ha c = true -> Hb c = true).
    intros a b H Ha Hb.
    unfold right_coset.
    intros [Ha_Coset Hb_Coset] Intersection.
    destruct Intersection as [x [Ha_x Hb_x]].
    destruct Ha_Coset as [H_subgroup Ha_h1].
    apply Ha_h1 in Ha_x.
    destruct Ha_x as [h1 [h1_subgroup h1_equality]].
    destruct Hb_Coset as [_ Hb_h2].
    apply Hb_h2 in Hb_x.
    destruct Hb_x as [h2 [h2_subgroup h2_equality]].
    intros c.
    (* show a = h1_inverse h2 b *)
    assert (exists h1_inverse, H h1_inverse = true /\
                               op h1_inverse (op h2 b) = a) as H1_Inverse.
    unfold is_subgroup in H_subgroup.
    destruct H_subgroup as [_ [_ H_inverses]].
    apply H_inverses in h1_subgroup.
    destruct h1_subgroup as [h1_inverse h1_inverse_property].
    exists h1_inverse.
    split.
    destruct h1_inverse_property; assumption.
    apply (group_cancel_l A op zero Group h1 _ _).
    rewrite <- (group_assoc A op zero Group).
    destruct h1_inverse_property as [_ H1_Inverse_Rewrite].
    rewrite H1_Inverse_Rewrite.
    rewrite (group_zero_l A op zero Group).
    rewrite h1_equality, h2_equality; reflexivity.
    destruct H1_Inverse as [h1_inverse [h1_inverse_subgroup h1_inverse_eq_a]].
    (* assert h1_inverse h2 is in the subgroup, then apply coset *)
    assert (H (op h1_inverse h2) = true) as h1_inverse_h2_In_Subgroup.
    unfold is_subgroup in H_subgroup.
    destruct H_subgroup as [_ [H_closed _]].
    assert (H h1_inverse = true /\ H h2 = true) as H'; auto.
    (* Ha c = true -> Hb c = true *)
    intros Ha_c.
    apply Ha_h1 in Ha_c.
    destruct Ha_c as [h [H_in_Subgroup Ha_c]].
    rewrite <- h1_inverse_eq_a in Ha_c.
    repeat rewrite <- (group_assoc A op zero Group) in Ha_c.
    apply (subgroup_op_closed h h1_inverse H H_subgroup H_in_Subgroup) in h1_inverse_subgroup.
    apply (subgroup_op_closed _ h2 H H_subgroup h1_inverse_subgroup) in h2_subgroup.
    apply (Hb_h2 c).
    exists (op (op h h1_inverse) h2).
    auto.
  Qed.

  Theorem coset_intersection:
    forall a b H Ha Hb,
      right_coset a H Ha /\ right_coset b H Hb ->
      (exists x, (Ha x = true /\ Hb x = true)) ->
                (forall c, Ha c = true <-> Hb c = true).
  Proof.
    intros a b H Ha Hb [Ha_Coset Hb_Coset] X_exists.
    split.
    apply (coset_intersection_helper a b H); auto.
    apply (coset_intersection_helper b a H); auto.
    destruct X_exists as [x [H1 H2]]; auto.
    exists x; auto.
  Qed.
End subgroups.

(* ring zero *)
(* ring id *)
(* ring mult *)
(* ring add *)
Definition is_ring (A: Set) := A -> A -> (A -> A -> A) -> (A -> A -> A).
