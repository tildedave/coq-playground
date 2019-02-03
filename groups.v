Require Import Coq.Bool.Bool.
Require Import Setoid.

Lemma bool_dec2 : forall b1 b2 b3 b4 : bool,
    {b1 = b2 /\ b3 = b4} + {b1 <> b2 /\ b3 = b4} + {b1 = b2 /\ b3 <> b4} + {b1 <> b2 /\ b3 <> b4}.
  intros b1 b2 b3 b4.
  destruct (bool_dec b1 b2) as [b1_eq_b2 | b1_neq_b2].
  destruct (bool_dec b3 b4) as [b3_eq_b4 | b3_neq_b4].
  auto.
  auto.
  destruct (bool_dec b3 b4) as [b3_eq_b4 | b3_neq_b4].
  auto.
  auto.
Qed.

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


Section groups.

  Variables (A : Set) (op : A -> A -> A) (inv : A -> A) (zero : A).
  Variable (Group : is_group A op inv zero).

  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Section group_laws.

  Lemma inverse1 (a: A): a <*> (inv a) = zero.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    apply HasInverse.
  Qed.

  Lemma inverse2 (a: A): (inv a) <*> a = zero.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    apply HasInverse.
  Qed.

  Lemma inverse_commutes (a: A): a <*> (inv a) = (inv a) <*> a.
    unfold is_group, is_inverse in Group.
    destruct Group as [_ HasInverse].
    rewrite inverse1. symmetry; apply HasInverse.
  Qed.

  Lemma group_add_l: forall a b c, b = c -> a <*> b = a <*> c.
    intros a b c.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma group_add_r: forall a b c, b = c -> b <*> a = c <*> a.
    intros a  b c.
    intros H; rewrite H; reflexivity.
  Qed.

  Lemma group_zero_r: forall a, a <*> zero = a.
    destruct Group as [[_ Zero] _]; apply Zero.
  Qed.

  Lemma group_zero_l: forall a, zero <*> a = a.
    destruct Group as [[_ Zero] _]; apply Zero.
  Qed.

  Lemma group_assoc: forall a b c, (a <*> b) <*> c = a <*> (b <*> c).
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

  Theorem inverse_cancel: forall a, inv (inv a) = a.
    intros a.
    (* show (inv a) * a = zero *)
    remember (inverse2 a) as H.
    destruct HeqH.
    apply inverse_unique in H.
    symmetry; assumption.
  Qed.

  Lemma inverse_apply: forall a b, inv (a <*> b) = inv b <*> inv a.
  Proof.
    intros a b.
    apply (group_cancel_l (a <*> b) _).
    rewrite <- group_assoc.
    rewrite inverse1.
    repeat rewrite group_assoc.
    rewrite <- (group_assoc b _ _).
    rewrite inverse1.
    rewrite group_zero_l.
    rewrite inverse1; reflexivity.
  Qed.

  Lemma inverse_swap: forall a b c, a = op (inv b) c <-> op b a = c.
  Proof.
    intros a b c.
    split.
    intros a_eq.
    apply (group_cancel_l (inv b)).
    rewrite <- group_assoc.
    rewrite inverse2.
    rewrite group_zero_l.
    assumption.
    intros c_eq.
    apply (group_cancel_l b).
    rewrite <- group_assoc.
    rewrite inverse1.
    rewrite group_zero_l.
    assumption.
  Qed.

  Lemma inverse_zero : inv zero = zero.
    apply (group_cancel_l zero).
    rewrite inverse1.
    rewrite group_zero_l.
    reflexivity.
  Qed.

  End group_laws.

  Hint Rewrite inverse_swap.
  Hint Rewrite inverse_zero.
  Hint Rewrite inverse1.
  Hint Rewrite inverse2.
  Hint Rewrite group_assoc.
  Hint Rewrite group_zero_l.
  Hint Rewrite group_zero_r.
  Hint Rewrite inverse_cancel.
  Hint Rewrite inverse_apply.

  Section subgroups.

    (* subgroup_mem is a characteristic function.  not sure if it will need to
     be A -> Prop instead of a -> bool. *)
    Definition is_subgroup (H: A -> bool) :=
      (* 0 is a subgroup member *)
      H zero = true /\
      (* subgroup is closed under operation *)
      (forall a b, H a = true /\ H b = true -> H (a <*> b) = true) /\
      (* if an element is in the subgroup, its inverse is too *)
      (forall a, H a = true -> H (inv a) = true).

    Definition is_mem (mem: A -> bool) (a : A) := mem a = true.

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

    Lemma subgroup_inverse1: forall a H, is_subgroup H -> is_mem H a -> is_mem H (inv a).
      intros a H IsSubgroup.
      unfold is_subgroup in IsSubgroup.
      destruct IsSubgroup as [_ [_ Inverse]].
      apply Inverse.
    Qed.

    Lemma subgroup_inverse2: forall a H, is_subgroup H -> is_mem H (inv a) -> is_mem H a.
      intros a H IsSubgroup H_inv_a.
      rewrite <- inverse_cancel.
      apply subgroup_inverse1.
      auto.
      assumption.
    Qed.

    Lemma subgroup_inverse: forall a H, is_subgroup H -> is_mem H (inv a) <-> is_mem H a.
    Proof.
      intros.
      split.
      apply subgroup_inverse2; auto.
      apply subgroup_inverse1; auto.
    Qed.

    Lemma subgroup_op_non_member_right: forall a b H,
        is_subgroup H -> H a = true /\ H b = false -> H (a <*> b) = false.
      intros a b H IsSubgroup Ha_true.
      (* Suppose ab were in the subgroup.  Then a^{-1} ab would be in the subgroup, so b is in the subgroup.
         contradiction *)
      destruct (bool_dec (H (a <*> b)) false) as [Hab_false | Hab_true].
      assumption.
      destruct Ha_true as [Ha_true Hb_false].
      apply not_false_is_true in Hab_true.
      apply (subgroup_op_closed (inv a) _ H IsSubgroup) in Hab_true.
      rewrite <- group_assoc in Hab_true.
      rewrite inverse2 in Hab_true.
      rewrite group_zero_l in Hab_true.
      unfold is_mem in Hab_true.
      rewrite Hb_false in Hab_true.
      contradict Hab_true.
      auto.
      apply (subgroup_inverse _ _ IsSubgroup).
      auto.
    Qed.

    Lemma subgroup_op_non_member_left: forall a b H,
        is_subgroup H -> H a = false /\ H b = true -> H (a <*> b) = false.
      intros a b H IsSubgroup [Ha_false Hb_true].
      (* not sure if there is a clever way to use right, so we just duplicate the logic above (for now) *)
      (* Suppose ab were in the subgroup.  Then abb^{-1} would be in the subgroup, so a is in the subgroup.
         contradiction *)
      destruct (bool_dec (H (a <*> b)) false) as [Hab_false | Hab_true].
      assumption.
      apply not_false_is_true in Hab_true.
      apply (subgroup_op_closed _ (inv b) H IsSubgroup) in Hab_true.
      autorewrite with core in Hab_true.
      unfold is_mem in Hab_true.
      rewrite Ha_false in Hab_true.
      contradict Hab_true.
      auto.
      apply (subgroup_inverse _ _ IsSubgroup).
      auto.
    Qed.

    Lemma subgroup_mem_l:
      forall a b H, is_subgroup H -> H a = true -> H (a <*> b) = H b.
      intros a b H IsSubgroup.
      intros Hb_true.
      (* want to reason like .... H b = true
       If H a = true, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (bool_dec (H b) true) as [Ha_true | Ha_false].
      rewrite Ha_true; apply (subgroup_op_closed _ _ H IsSubgroup Hb_true Ha_true).
      apply not_true_is_false in Ha_false.
      rewrite Ha_false.
      apply (subgroup_op_non_member_right a b H IsSubgroup).
      auto.
    Qed.

    Lemma subgroup_mem_r:
      forall a b H, is_subgroup H -> H b = true -> H (a <*> b) = H a.
      intros a b H IsSubgroup.
      intros Hb_true.
      (* want to reason like .... H b = true
       If H a = true, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (bool_dec (H a) true) as [Ha_true | Ha_false].
      rewrite Ha_true; apply (subgroup_op_closed _ _ H IsSubgroup Ha_true Hb_true).
      apply not_true_is_false in Ha_false.
      rewrite Ha_false.
      apply (subgroup_op_non_member_left a b H IsSubgroup).
      auto.
    Qed.

    Lemma subgroup_inverse_non_member1: forall a H, is_subgroup H -> H a = false -> H (inv a) = false.
      intros a H IsSubgroup.
      intros Ha_false.
      destruct (bool_dec (H (inv a)) true) as [Ha_inv_true | Ha_inv_false].
      apply (subgroup_inverse _ _ IsSubgroup) in Ha_inv_true.
      rewrite inverse_cancel in Ha_inv_true.
      unfold is_mem in Ha_inv_true.
      rewrite Ha_false in Ha_inv_true.
      contradict Ha_inv_true.
      auto.
      apply not_true_is_false in Ha_inv_false; auto.
    Qed.

    Lemma subgroup_inverse_non_member2: forall a H, is_subgroup H -> H (inv a) = false -> H a = false.
      intros a H IsSubgroup.
      intros Ha_inv_false.
      apply (subgroup_inverse_non_member1 (inv a) H IsSubgroup) in Ha_inv_false.
      rewrite <- (inverse_cancel a).
      assumption.
    Qed.

  End subgroups.

  Section cosets.

    (* c \in aH if b \in H such that ab = c, b = a^{-1}c *)
    Definition left_coset (a: A) (H: A -> bool) := fun c => H ((inv a) <*> c).
    (* c \in Ha if b \in H such that ba = c, b = c a^{-1} *)
    Definition right_coset (H: A -> bool) (a: A) := fun c => H (c <*> (inv a)).

    Lemma coset_intersection_helper_1:
      forall a b H,
        is_subgroup H ->
        (exists x, is_mem (right_coset H a) x /\  is_mem (right_coset H b) x) ->
        exists h1 h2, is_mem H h1 /\ is_mem H h2 /\ a = op (op (inv h1) h2) b.
      intros a b H IsSubgroup [x [Ha_x Hb_x]].
      unfold is_mem, right_coset, left_coset in Ha_x, Hb_x.
      exists (x <*> inv a), (x <*> inv b).
      split; [assumption | split; [assumption | auto]].
      rewrite inverse_apply.
      repeat rewrite group_assoc.
      rewrite <- (group_assoc (inv x) _ _).
      repeat rewrite inverse2.
      rewrite inverse_cancel.
      repeat rewrite group_zero_r.
      reflexivity.
    Qed.

    (* a in Hb -> Ha = Hb *)
    Lemma coset_intersection:
      forall a b H,
        is_subgroup H ->
        (exists x, is_mem (right_coset H a) x /\  is_mem (right_coset H b) x) ->
        (forall c, (right_coset H a) c = (right_coset H b) c).
      intros a b H IsSubgroup Intersection.
      apply (coset_intersection_helper_1 a b H IsSubgroup) in Intersection.
      destruct Intersection as [h1 [h2 [h1_Subgroup [h2_Subgroup a_definition]]]].
      intros c.
      unfold right_coset.
      rewrite a_definition.
      repeat rewrite inverse_apply.
      rewrite inverse_cancel.
      rewrite <- group_assoc.
      apply (subgroup_inverse1 h2 H IsSubgroup) in h2_Subgroup.
      apply (subgroup_op_closed (inv h2) h1 H IsSubgroup h2_Subgroup) in h1_Subgroup.
      apply (subgroup_mem_r _ (inv h2 <*> h1) H IsSubgroup).
      assumption.
    Qed.

    Lemma coset_reflexive: forall a H, is_subgroup H -> right_coset H a a = true.
    Proof.
      intros a H IsSubgroup.
      unfold right_coset.
      rewrite inverse1.
      apply IsSubgroup.
    Qed.

    Theorem coset_representative:
      forall a b H,
        is_subgroup H -> right_coset H b a = true ->
        forall c, right_coset H a c = right_coset H b c.
    Proof.
      intros a b H IsSubgroup.
      intros Hb_a.
      (* going to show that a is in both Ha Hb *)
      remember (coset_reflexive a H IsSubgroup) as Ha_a.
      apply (coset_intersection a b H IsSubgroup); auto.
      exists a; auto.
    Qed.

    Theorem coset_mult: forall a b H, is_subgroup H -> is_mem H b -> is_mem (right_coset H a) (op b a).
      intros a b H IsSubgroup Hb_true.
      unfold right_coset, is_mem.
      autorewrite with core.
      auto.
    Qed.

    Theorem coset_zero:
      forall a H, is_subgroup H -> is_mem H a -> forall c, right_coset H a c = right_coset H zero c.
    Proof.
      intros a H IsSubgroup Ha_true.
      (* WTS: everything in Ha can be represented by something in H *)
      unfold right_coset.
      intros c.
      apply (subgroup_inverse _ _ IsSubgroup) in Ha_true.
      rewrite (subgroup_mem_r _ _ H IsSubgroup).
      autorewrite with core.
      reflexivity.
      auto.
    Qed.

  End cosets.

  Section normal_subgroups.

    Definition is_normal_subgroup (H: A -> bool) :=
      is_subgroup H /\ forall (a h : A), is_mem H h -> is_mem H (a <*> h <*> inv a).

    Lemma normal_subgroup_intro: forall a h H,
        is_normal_subgroup H -> is_mem H h ->
        is_mem H (a <*> h <*> inv a).
      intros a h H IsNormalSubgroup h_Subgroup.
      destruct IsNormalSubgroup as [IsSubgroup Normality].
      apply Normality.
      assumption.
    Qed.

    Lemma normal_subgroup_conjuation: forall a h H,
        is_normal_subgroup H -> is_mem H h ->
        is_mem H (a <*> h <*> inv a) <-> is_mem H ((inv a) <*> h <*> a).
    Proof.
      intros a h H IsNormalSubgroup h_Subgroup.
      (* inv (a b) = inv b inv a *)
      destruct IsNormalSubgroup as [IsSubgroup h_Membership].
      split.
      intros a_h_inv_a_Subgroup.
      rewrite <- (inverse_cancel a) at 2.
      apply (h_Membership (inv a)).
      assumption.
      intros inv_a_h_a_Subgroup.
      apply h_Membership.
      assumption.
    Qed.

    Theorem normal_subgroup_membership_commutes : forall a b H,
        is_normal_subgroup H -> H (a <*> b) = H (b <*> a).
      intros a b H IsNormalSubgroup.
      assert (is_subgroup H) as IsSubgroup. destruct IsNormalSubgroup; auto.
      destruct (bool_dec2 (H a) true (H b) true) as
          [[[[Ha_true Hb_true] | [Ha_false Hb_true]] |
            [Ha_true Hb_false]] | [Ha_false Hb_false]].
      assert (H b = true) as Hb_true2. assumption.
      apply (subgroup_op_closed a b H IsSubgroup Ha_true) in Hb_true.
      apply (subgroup_op_closed b a H IsSubgroup Hb_true2) in Ha_true.
      unfold is_mem in Ha_true, Hb_true.
      rewrite Ha_true, Hb_true.
      reflexivity.
      apply not_true_is_false in Ha_false.
      rewrite (subgroup_op_non_member_left a _ _ IsSubgroup),
      (subgroup_op_non_member_right _ a _ IsSubgroup).
      reflexivity.
      auto.
      auto.
      apply not_true_is_false in Hb_false.
      rewrite (subgroup_op_non_member_left b _ _ IsSubgroup),
      (subgroup_op_non_member_right _ b _ IsSubgroup).
      reflexivity.
      auto.
      auto.
      (* this is silly but I need this later I think *)
      assert (is_normal_subgroup H) as IsNormalSubgroup2. assumption.
      destruct (bool_dec (H (a <*> b)) true) as [Hab_true | Hab_false].
      rewrite Hab_true; symmetry.
      (* ab \in H, WTS ba in H.  a^{-1}aba \in H *)
      apply (normal_subgroup_intro (inv a)) in Hab_true.
      autorewrite with core in Hab_true.
      rewrite <- group_assoc, inverse2, group_zero_l in Hab_true.
      assumption.
      assumption.
      apply not_true_is_false in Hab_false.
      destruct (bool_dec (H (b <*> a)) true) as [Hba_true | Hba_false].
      (* ba \in H, WTS ab in H (contradiction). b^{-1}bab \in H  *)
      destruct IsNormalSubgroup as [_ Normality].
      apply (Normality (inv b) _) in Hba_true.
      autorewrite with core in Hba_true.
      rewrite <- group_assoc, inverse2, group_zero_l in Hba_true.
      contradict Hba_true.
      unfold is_mem.
      apply not_true_iff_false.
      assumption.
      apply not_true_is_false in Hba_false.
      rewrite Hab_false, Hba_false; reflexivity.
    Qed.

    Theorem normal_subgroup_left_coset_iff_right_coset : forall a H,
        is_normal_subgroup H ->
        forall c, left_coset a H c = right_coset H a c.
    Proof.
      intros a H IsNormalSubgroup.
      assert (is_subgroup H) as IsSubgroup.  destruct IsNormalSubgroup; auto.
      intros c.
      unfold left_coset.
      unfold right_coset.
      apply normal_subgroup_membership_commutes.
      assumption.
    Qed.

    Lemma normal_subgroup_coset_op : forall a b c d H,
        is_normal_subgroup H ->
        is_mem (right_coset H a) c -> is_mem (right_coset H b) d -> is_mem (right_coset H (a <*> b)) (c <*> d).
      intros a b c d H IsNormalSubgroup.
      assert (is_subgroup H) as IsSubgroup.  destruct IsNormalSubgroup; auto.
      unfold is_mem, right_coset.
      intros c_Coset d_Coset.
      rewrite (normal_subgroup_membership_commutes _ _ H IsNormalSubgroup) in c_Coset.
      fold (is_mem H (inv a <*> c)) in c_Coset.
      fold (is_mem H (d <*> inv b)) in d_Coset.
      apply (subgroup_op_closed _ _ H IsSubgroup c_Coset) in d_Coset.
      rewrite group_assoc in d_Coset.
      rewrite <- (group_assoc c d _) in d_Coset.
      unfold is_mem in d_Coset.
      rewrite (normal_subgroup_membership_commutes (inv a) _ H IsNormalSubgroup) in d_Coset.
      rewrite inverse_apply.
      rewrite <- group_assoc.
      assumption.
    Qed.
  End normal_subgroups.

  Section homomorphisms.
    Definition is_homomorphism (A: Set) op inv zero (B: Set) op' inv' zero' (h: A -> B) :=
      is_group A op inv zero /\
      is_group B op' inv' zero' /\
      h zero = zero' /\
      forall a b,
        h (op a b) = op' (h a) (h b).

    Lemma id_homomorphism : is_homomorphism A op inv zero A op inv zero (fun a => a).
      unfold is_homomorphism.
      auto.
    Qed.

    Lemma abelian_group_inv_homomorphism :
      is_abelian_group A op inv zero ->
      is_homomorphism A op inv zero A op inv zero (fun a => (inv a)).
    Proof.
      unfold is_abelian_group, is_commutative.
      intros [_ IsCommutative].
      unfold is_homomorphism.
      split; [assumption | split; [assumption | split; [apply inverse_zero|auto]]].
      intros a b.
      rewrite IsCommutative, inverse_apply; reflexivity.
    Qed.

  End homomorphisms.

  (* Universe of quotient groups is the coset universe, e.g. A -> bool *)

  Definition Coset (H: A -> bool) (a : A) : Set :=
    is_group A op inv zero /\ is_normal_subgroup H.


  Definition quotient_group_zero (H : A -> bool) := H.
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

End groups.

Check Coset.
