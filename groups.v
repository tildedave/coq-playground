(* a ring is a set with various properties
   ring_mult
   ring_add
 *)

Section group_definitions.
  Definition is_assoc (A: Set) (f: A -> A -> A) := forall a b c,
    f (f a b) c = f a (f b c).

  Definition is_commutative (A: Set) (f: A -> A -> A) := forall a b, f a b = f b a.

  Definition is_inverse (A: Set) (f: A -> A -> A) (inv: A -> A) (z: A) :=
    forall a, f a (inv a) = z /\ f (inv a) a = z.

  Definition is_zero (A: Set) (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

  Definition is_semigroup (A: Set) (op: A -> A -> A) (zero: A) := (is_assoc A op) /\ (is_zero A op zero).

  Definition is_group (A: Set) (op: A -> A -> A) (inv: A -> A) (zero: A) :=
    is_semigroup A op zero /\ is_inverse A op inv zero.

  Definition is_abelian_group (A: Set) (op: A -> A -> A) (inv: A -> A) (zero: A) :=
    is_group A op inv zero /\ is_commutative A op.

End group_definitions.

Section group_laws.

  Variables (A : Set) (op : A -> A -> A) (inv : A -> A) (zero : A).
  Variable (Group : is_group A op inv zero).

  Lemma inverse1 (a: A): op a (inv a) = zero.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    apply HasInverse.
  Qed.

  Lemma inverse2 (a: A): op (inv a) a = zero.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    apply HasInverse.
  Qed.

  Lemma inverse_commutes (a: A): op a (inv a) = op (inv a) a.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    rewrite inverse1. symmetry; apply HasInverse.
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
    intros a b c OpABEqOpAC.
    rewrite <- (group_zero_l b), <- (group_zero_l c).
    rewrite <- (inverse2 a).
    repeat rewrite group_assoc.
    apply (group_add_l (inv a)).
    assumption.
  Qed.

  Lemma group_cancel_r: forall a b c, op b a = op c a -> b = c.
    intros a b c OpABEqOpAC.
    rewrite <- (group_zero_r b), <- (group_zero_r c).
    rewrite <- (inverse1 a).
    repeat rewrite <- group_assoc.
    apply (group_add_r (inv a)).
    assumption.
  Qed.

  Theorem id_is_unique: forall a, (forall b, op a b = b) -> a = zero.
    intros a ADef.
    apply (group_cancel_r (inv a)).
    rewrite group_zero_l; apply ADef.
  Qed.

  Theorem op_zero_commutes: forall a b, op a b = zero <-> op b a = zero.
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

  Theorem inverse_unique: forall a b, op a b = zero -> b = inv a.
    intros a b.
    intros OpABZero.
    apply (group_cancel_l a _ _).
    rewrite inverse1.
    assumption.
  Qed.
End group_laws.

Section subgroups.
  Variables (A : Set) (op : A -> A -> A) (inv : A -> A) (zero : A).
  Variable (Group : is_group A op inv zero).

  (* subgroup_mem is a characteristic function.  not sure if it will need to
     be A -> Prop instead of a -> bool. *)
  Definition is_subgroup (subgroup_mem: A -> bool) :=
    (* 0 is a subgroup member *)
    subgroup_mem zero = true /\
    (* subgroup is closed under operation *)
    (forall a b, subgroup_mem a = true /\ subgroup_mem b = true ->
                 subgroup_mem (op a b) = true) /\
    (* if an element is in the subgroup, its inverse is too *)
    (forall a, subgroup_mem a = true -> subgroup_mem (inv a) = true).

  Definition is_mem (mem: A -> bool) (a : A) := mem a = true.

  Definition left_coset (a: A) (H: A -> bool) (aH: A -> bool) :=
    is_subgroup H /\ forall (c: A), is_mem aH c <-> exists b, is_mem H b /\ (op a b) = c.

  Definition right_coset (a: A) (H: A -> bool) (Ha: A -> bool) :=
    is_subgroup H /\ forall (c: A), is_mem Ha c <-> exists b, is_mem H b /\ (op b a)  = c.

  Lemma subgroup_op_closed: forall a b H,
      is_subgroup H -> is_mem H a -> is_mem H b -> is_mem H (op a b).
  Proof.
    intros a b H.
    unfold is_subgroup.
    intros [_ [H_closed _]].
    intros Ha Hb.
    apply H_closed.
    auto.
  Qed.

  Lemma inverse_subgroup: forall a H,
      is_subgroup H -> is_mem H a -> is_mem H (inv a).
    intros a H IsSubgroup H_a.
    unfold is_subgroup in IsSubgroup.
    destruct IsSubgroup as [_ [_ Inverse]].
    apply (Inverse a); assumption.
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

  Lemma coset_reflexive: forall a H Ha, right_coset a H Ha -> Ha a = true.
  Proof.
    intros a H Ha.
    intros Ha_coset.
    unfold right_coset in Ha_coset.
    destruct Ha_coset as [H_subgroup HCoset_membership].
    unfold is_subgroup in H_subgroup.
    destruct H_subgroup as [H_zero [H_closed _]].
    apply (HCoset_membership a).
    exists zero.
    split; auto.
    rewrite (group_zero_l A op zero Group); reflexivity.
  Qed.

  Theorem coset_representative:
    forall a b H Ha Hb,
      right_coset a H Ha /\ right_coset b H Hb ->
      Hb a = true ->
      forall c, Ha c = true <-> Hb c = true.
  Proof.
    intros a b H Ha Hb [Ha_Coset Hb_Coset].
    intros Hb_a.
    (* going to show that a is in both Ha Hb *)
    remember (coset_reflexive a H Ha Ha_Coset) as Ha_a.
    apply (coset_intersection a b H Ha Hb); auto.
    exists a; auto.
  Qed.

  Theorem coset_inverse:
    forall a b H Ha,
      right_coset a H Ha -> Ha b = true -> (exists h, H h = true /\ op h a = b).
    intros a b H Ha.
    intros Ha_coset.
    unfold right_coset in Ha_coset.
    destruct Ha_coset as [H_subgroup Ha_coset].
    apply (Ha_coset b).
  Qed.

  Theorem coset_mult: forall a b H Ha, right_coset a H Ha -> H b = true -> Ha (op b a) = true.
    intros a b H Ha Ha_Coset Hb_true.
    apply Ha_Coset.
    exists b; auto.
  Qed.

  Theorem coset_zero:
    forall a H Ha,
      H a = true -> right_coset a H Ha -> right_coset zero H Ha.
  Proof.
    intros a H Ha Ha_true Ha_Coset.
    assert (is_subgroup H) as IsSubgroup.
    unfold right_coset in Ha_Coset; destruct Ha_Coset; auto.
    remember (inverse_subgroup a H IsSubgroup Ha_true) as HA.
    destruct HA as [a_inverse [H_a_inverse op_a_a_inverse_eq_zero]].
    split.
    assumption.
    intros c.
    split; intro Ha_c_true.
    exists c; split.
    apply (coset_inverse _ c H Ha) in Ha_Coset.
    destruct Ha_Coset as [h [h_Subgroup h_op_a]].
    rewrite <- h_op_a; apply (subgroup_op_closed h a H IsSubgroup h_Subgroup Ha_true).
    assumption.
    apply (group_zero_r A op zero Group).
    destruct Ha_c_true as [c' [H_c' Heqc']].
    rewrite (group_zero_r A op zero Group) in Heqc'.
    (* showing that c is in the coset, assumption c is in the group *)
    assert (H c = true) as Hc.  rewrite <- Heqc'. assumption.
    (* I've lost the thread, I assume we must conjugate c *)
    (* Show c * a^1 * a = c *)
    destruct HeqHA.
    apply (subgroup_op_closed c a_inverse H IsSubgroup Hc) in H_a_inverse.
    (* want to transform right_coset a H Ha and H (op c a_inverse) = true into Ha c = true *)
    (* right_coset a H Ha -> H b -> Ha (b a) *)
    apply (coset_mult _ (op c a_inverse) H Ha Ha_Coset) in H_a_inverse.
    rewrite <- (group_zero_r A op zero Group c).
    apply (inverse_commutes A op zero Group) in op_a_a_inverse_eq_zero.
    rewrite <- op_a_a_inverse_eq_zero.
    repeat rewrite <- (group_assoc A op zero Group).
    assumption.
  Qed.

  (* all the same facts are true for left cosets but I don't want to prove those now :) *)

  (* TODO: normal subgroup *)
  (* TODO: group mod subgroup *)
  (* Show: group mod normal subgroup is a group *)

End subgroups.

Section quotient_groups.
  Variables (A : Set) (op : A -> A -> A) (zero : A).
  Variable (Group : is_group A op zero).
  Variable (H: A -> bool).
  Variable (Subgroup: is_subgroup A op zero H).

  (* Universe of quotient groups is the coset universe, e.g. A -> bool *)

  Definition quotient_group_zero := H.
    (* zero is coset based on subgroup membership *)

  Definition quotient_group_op (a b: (A -> bool)) :=
    (* a is one coset,
       b is another coset
       Ha Hb = H(ab).
       Do we know this without a or b?  ;)
       Maybe we need the cosets to come with their proofs that they are cosets.
     *)
    a.


  (* theorem should show is_group holds for a given quotient_group *)

End quotient_groups.


(* ring zero *)
(* ring id *)
(* ring mult *)
(* ring add *)
Definition is_ring (A: Set) := A -> A -> (A -> A -> A) -> (A -> A -> A).
