Require Import Coq.Bool.Bool.
Require Import Setoid.
Require Import Coq.Classes.Equivalence.

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
    forall a,  f a (inv a) = z /\ f (inv a) a = z.

  Definition is_zero (A: Set) (f: A -> A -> A) (z: A) := forall a, f a z = a /\ f z a = a.

  Definition is_semigroup (A: Set) (op: A -> A -> A) (zero: A) := (is_assoc A op) /\ (is_zero A op zero).

  Definition is_group (A: Set) (op: A -> A -> A) (inv: A -> A) (zero: A) :=
    is_semigroup A op zero /\ is_inverse A op inv zero.

  Definition is_abelian_group (A: Set) (op: A -> A -> A) (inv: A -> A) (zero: A) :=
    is_group A op inv zero /\ is_commutative A op.

End group_definitions.

Section groups.
  Structure Group : Type := makeGroup
    {
      A :> Set;

      op : A -> A -> A ;
      inv : A -> A ;
      zero : A ;

      op_assoc : forall a b c, op a (op b c) = op (op a b) c;
      op_zero : forall a, op a zero = a /\ op zero a = a ;
      op_inverse : forall a, op a (inv a) = zero /\ op (inv a) a = zero
    }.

  Arguments zero {g}.
  Arguments op {g} _ _.
  Arguments inv {g} _.

  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Variable (G : Group).

  Lemma inverse1 : forall (a : G), a <*> (inv a) = zero.
    apply op_inverse.
  Qed.

  Lemma inverse2 : forall (a: G), (inv a) <*> a = zero.
    apply op_inverse.
  Qed.

  Lemma inverse3 : forall (a b : G), inv a <*> (a <*> b) = b.
    intros.
    rewrite op_assoc, inverse2.
    apply op_zero.
  Qed.

  Lemma inverse4 : forall (a b : G), a <*> (inv a <*> b) = b.
    intros.
    rewrite op_assoc, inverse1.
    apply op_zero.
  Qed.

  Hint Rewrite inverse1.
  Hint Rewrite inverse2.
  Hint Rewrite inverse3.
  Hint Rewrite inverse4.

  Lemma inverse_commutes : forall (a: G), a <*> (inv a) = (inv a) <*> a.
    intros; autorewrite with core; auto.
  Qed.

  Lemma group_add_l: forall (a b c : G), b = c -> a <*> b = a <*> c.
    intros; rewrite H; auto.
  Qed.

  Lemma group_add_r: forall (a b c : G), b = c -> b <*> a = c <*> a.
    intros; rewrite H; auto.
  Qed.

  Lemma group_zero_r: forall (a : G), a <*> zero = a.
    apply op_zero.
  Qed.

  Lemma group_zero_l: forall (a : G), zero <*> a = a.
    apply op_zero.
  Qed.

  Lemma group_assoc: forall (a b c : G), (a <*> b) <*> c = a <*> (b <*> c).
    intros; rewrite op_assoc; reflexivity.
  Qed.

  Hint Rewrite group_zero_r.
  Hint Rewrite group_zero_l.
  Hint Rewrite group_assoc.

  Lemma group_cancel_l: forall (a b c : G), a <*> b = a <*> c -> b = c.
    intros a b c OpABEqOpAC.
    rewrite <- (group_zero_l b), <- (group_zero_l c).
    rewrite <- (inverse2 a).
    repeat rewrite group_assoc.
    apply (group_add_l (inv a)).
    assumption.
  Qed.

  Lemma group_cancel_r: forall (a b c :G), b <*> a = c <*> a -> b = c.
    intros a b c OpABEqOpAC.
    rewrite <- (group_zero_r b), <- (group_zero_r c).
    rewrite <- (inverse1 a).
    repeat rewrite <- group_assoc.
    apply (group_add_r (inv a)).
    assumption.
  Qed.

  Theorem id_is_unique: forall a : G, (forall b : G, a <*> b = b) -> a = zero.
    intros a ADef.
    apply (group_cancel_r (inv a)).
    rewrite group_zero_l; apply ADef.
  Qed.

  Theorem op_zero_commutes: forall (a b : G), a <*> b = zero <-> b <*> a = zero.
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

  Theorem inverse_unique: forall (a b : G), a <*> b = zero -> b = inv a.
    intros a b.
    intros OpABZero.
    apply (group_cancel_l a _ _).
    rewrite inverse1.
    assumption.
  Qed.

  Theorem inverse_cancel: forall (a : G), inv (inv a) = a.
    intros a.
    (* show (inv a) * a = zero *)
    remember (inverse2 a) as H.
    destruct HeqH.
    apply inverse_unique in H.
    symmetry; assumption.
  Qed.

  Hint Rewrite inverse_cancel.

  Lemma inverse_apply: forall (a b : G), inv (a <*> b) = inv b <*> inv a.
  Proof.
    intros a b.
    apply (group_cancel_l (a <*> b) _).
    rewrite <- group_assoc, inverse1.
    repeat rewrite group_assoc.
    rewrite inverse4, inverse1.
    reflexivity.
  Qed.

  Lemma inverse_swap: forall (a b c : G), a = (inv b) <*> c <-> b <*> a = c.
  Proof.
    intros a b c.
    split.
    intros a_eq.
    apply (group_cancel_l (inv b)).
    rewrite inverse3; assumption.
    intros.
    apply (group_cancel_l b).
    rewrite inverse4; assumption.
  Qed.

  Lemma inverse_zero: @inv G zero = zero.
    apply (group_cancel_l zero).
    rewrite inverse1, group_zero_l.
    reflexivity.
  Qed.

  Hint Rewrite inverse_zero.

  Section group_examples.
    Require Import Coq.ZArith.BinInt.
    Require Import ZArithRing.
    Local Open Scope Z_scope.
    Check Group.

    Definition integer_group : Group.
      remember (fun n => -n) as inv.
      assert (forall a b c : Z, a + (b + c) = a + b + c) as Z_assoc.
      intros; ring.
      assert (forall a : Z, a + Z.zero = a /\ Z.zero + a = a) as Z_zero.
      intros; rewrite Z.add_0_r, Z.add_0_l; auto.
      assert (forall a : Z, a + (fun n => -n) a = Z.zero /\ (fun n => -n) a + a = Z.zero) as Z_inv.
      intros; rewrite Z.add_opp_diag_r, Z.add_opp_diag_l. auto.
      exact (makeGroup Z Z.add (fun n => - n) Z.zero Z_assoc Z_zero Z_inv).
    Defined.

    Check integer_group.

  Section subgroups.

    Definition set (A : Set) := A -> bool.

    Definition is_mem (A: Set) (H: set A) (a : A) := H a = true.

    Arguments is_mem {A} _ _.

    Theorem is_mem_dec (A : Set) (H : set A) :
      forall a, { is_mem H a } +  { ~(is_mem H a) }.
      unfold is_mem. intros a.
      apply (bool_dec (H a)).
    Qed.

    Theorem is_mem_contradict (A : Set) (H : set A) :
      forall a, is_mem H a -> ~is_mem H a -> False.
      intros a; auto.
    Qed.

    Theorem is_mem_not (A : Set) (H : set A):
      forall a, ~is_mem H a -> (H a) = false.
      intros a not_mem.
      unfold is_mem in not_mem.
      rewrite <- not_true_iff_false.
      assumption.
    Qed.


  (* subgroup_mem is a characteristic function.
     TODO: figure out how to do this nicer ;)
   *)
    Definition is_subgroup (G : Group) (H: set G) :=
      (* 0 is a subgroup member *)
      is_mem H zero /\
      (* subgroup is closed under operation *)
      (forall a b, is_mem H a /\ is_mem H b -> is_mem H (a <*> b)) /\
      (* if an element is in the subgroup, its inverse is too *)
      forall a, is_mem H a -> is_mem H (inv a).

    Arguments is_subgroup {G} _.

    (* H is a subgroup *)
    (* H is inductively defined, zero is in it,
       if a is in it, inv a is in it, if a b is in it, a op b is in it
       zero is a consequence of the other two
     *)

    Lemma subgroup_closed1: forall (a b : G) (H: set G),
        is_subgroup H -> is_mem H a -> is_mem H b -> is_mem H (a <*> b).
    Proof.
      intros a b H IsSubgroup.
      destruct IsSubgroup as [_ [H_closed _]].
      intros; apply H_closed; auto.
    Qed.

    Lemma subgroup_closed2: forall (a b : G) (H: set G),
        is_subgroup H -> is_mem H a -> is_mem H b -> is_mem H (b <*> a).
    Proof.
      intros a b H IsSubgroup.
      destruct IsSubgroup as [_ [H_closed _]].
      intros; apply H_closed; auto.
    Qed.

    Lemma subgroup_inverse1: forall (a : G) (H: set G),
        is_subgroup H -> is_mem H a -> is_mem H (inv a).
      intros a H IsSubgroup.
      destruct IsSubgroup as [_ [_ Inverse]]; apply Inverse.
    Qed.

    Lemma subgroup_inverse2: forall (a : G) (H: set G),
        is_subgroup H -> is_mem H (inv a) -> is_mem H a.
      intros a H IsSubgroup H_inv_a.
      rewrite <- inverse_cancel.
      apply subgroup_inverse1; auto.
    Qed.

    Lemma subgroup_inverse: forall (a : G) (H: set G),
        is_subgroup H -> is_mem H (inv a) <-> is_mem H a.
    Proof.
      intros. split.
      apply subgroup_inverse2; auto.
      apply subgroup_inverse1; auto.
    Qed.

    Lemma subgroup_op_non_member_right: forall a b (H: set G),
        is_subgroup H -> is_mem H a -> ~is_mem H b -> ~is_mem H (a <*> b).
      intros a b H IsSubgroup Ha_mem Hb_not_mem.
      (* Suppose ab were in the subgroup.  Then a^{-1} ab would be in the subgroup, so b is in the subgroup.
         contradiction *)
      destruct (is_mem_dec _ H (a <*> b)) as [Hab_mem | Hab_not_mem].
      apply (subgroup_closed1 (inv a) _ H IsSubgroup) in Hab_mem.
      rewrite <- group_assoc, inverse2, group_zero_l in Hab_mem; auto.
      apply (subgroup_inverse _ _ IsSubgroup); assumption.
      assumption.
    Qed.

    Lemma subgroup_op_non_member_left: forall a b (H: set G),
        is_subgroup H -> is_mem H b -> ~is_mem H a -> ~is_mem H (a <*> b).
      intros a b H IsSubgroup Hb_mem Ha_not_mem.
      (* not sure if there is a clever way to use right, so we just duplicate the logic above (for now) *)
      (* Suppose ab were in the subgroup.  Then a^{-1} ab would be in the subgroup, so b is in the subgroup.
         contradiction *)
      destruct (is_mem_dec _ H (a <*> b)) as [Hab_mem | Hab_not_mem].
      apply (subgroup_closed1 _ (inv b) H IsSubgroup) in Hab_mem.
      rewrite group_assoc, inverse1, group_zero_r in Hab_mem; auto.
      apply (subgroup_inverse _ _ IsSubgroup); assumption.
      assumption.
    Qed.

    Lemma subgroup_mem_l:
      forall a b (H : set G),
        is_subgroup H -> is_mem H a -> is_mem H (a <*> b) <-> is_mem H b.
      intros a b H IsSubgroup Ha_mem.
      (* want to reason like .... is_mem H b
       If is_mem H a, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (is_mem_dec _ H b) as [Hb_mem | Hb_not_mem].
      remember (subgroup_closed1 _ _ H IsSubgroup Ha_mem Hb_mem).
      split; [intros; assumption | intros; assumption].
      (* a is member, b not member, so these are proofs by contradiction *)
      remember (subgroup_op_non_member_right a b _ IsSubgroup Ha_mem Hb_not_mem) as Hab_not_mem.
      split.
      intros Hab_mem.
      contradict (is_mem_contradict _ _ _ Hab_mem Hab_not_mem).
      intros Hb_mem.
      contradict (is_mem_contradict _ _ _ Hb_mem Hb_not_mem).
    Qed.

    Lemma subgroup_mem_r: forall a b (H : set G),
        is_subgroup H -> is_mem H b -> is_mem H (a <*> b) <-> is_mem H a.
      intros a b H IsSubgroup Hb_mem.
      (* want to reason like .... is_mem H b
       If is_mem H a, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (is_mem_dec _ H a) as [Ha_mem | Ha_not_mem].
      remember (subgroup_closed1 _ _ H IsSubgroup Ha_mem Hb_mem).
      split; [intros; assumption | intros; assumption].
      (* a is member, b not member, so these are proofs by contradiction *)
      remember (subgroup_op_non_member_left a b _ IsSubgroup Hb_mem Ha_not_mem) as Hab_not_mem.
      split.
      intros Hab_mem.
      contradict (is_mem_contradict _ _ _ Hab_mem Hab_not_mem).
      intros Ha_mem.
      contradict (is_mem_contradict _ _ _ Ha_mem Ha_not_mem).
    Qed.

    Lemma subgroup_inverse_non_member1: forall a (H: set G),
        is_subgroup H -> ~is_mem H a -> ~is_mem H (inv a).
      intros a H IsSubgroup.
      destruct (is_mem_dec _ H (inv a)) as [Ha_inv_true | Ha_inv_false].
      apply (subgroup_inverse _ _ IsSubgroup) in Ha_inv_true.
      rewrite inverse_cancel in Ha_inv_true.
      intro Ha_false.
      contradict (is_mem_contradict _ _ _ Ha_inv_true Ha_false).
      intros; auto.
    Qed.

    Lemma subgroup_inverse_non_member2: forall a (H: set G),
        is_subgroup H -> ~is_mem H (inv a) -> ~is_mem H a.
      intros a H IsSubgroup.
      intros Ha_inv_false.
      apply (subgroup_inverse_non_member1 (inv a) H IsSubgroup) in Ha_inv_false.
      rewrite <- (inverse_cancel a).
      assumption.
    Qed.

  End subgroups.

  Section cosets.

    (* c \in aH if b \in H such that ab = c, b = a^{-1}c *)
    Definition left_coset (G: Group) (a : G) (H: set G) : set G := fun c => H ((inv a) <*> c).
    (* c \in Ha if b \in H such that ba = c, b = c a^{-1} *)
    Definition right_coset (G: Group) (H: set G) (a: G) : set G := fun c => H (c <*> (inv a)).

    Arguments is_mem {A} _ _.
    Arguments is_subgroup {G} _.
    Arguments right_coset {G} _.
    Arguments left_coset {G} _.

    Check right_coset.

    Lemma coset_intersection_helper_1:
      forall a b (H: set G),
        is_subgroup H ->
        (exists x, is_mem (right_coset H a) x /\  is_mem (right_coset H b) x) ->
        exists h1 h2, is_mem H h1 /\ is_mem H h2 /\ a = op (op (inv h1) h2) b.
      intros a b H IsSubgroup [x [Ha_x Hb_x]].
      unfold right_coset, left_coset in Ha_x, Hb_x.
      exists (x <*> inv a), (x <*> inv b).
      split; [assumption | split; [assumption | auto]].
      rewrite inverse_apply.
      autorewrite with core; reflexivity.
    Qed.

    (* a in Hb -> Ha = Hb *)
    Lemma coset_intersection:
      forall a b (H : set G),
        is_subgroup H ->
        (exists x, is_mem (right_coset H a) x /\ is_mem (right_coset H b) x) ->
        (forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c).
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
      apply (subgroup_closed1 (inv h2) h1 H IsSubgroup h2_Subgroup) in h1_Subgroup.
      (* must get rid of the coset definitions in order to apply
         subgroup_mem_r *)
      unfold is_mem.
      rewrite group_assoc.
      rewrite <- (group_assoc c _ _).
      fold (@is_mem (A G) H (c <*> (inv b <*> inv h2 <*> h1))).
      fold (@is_mem (A G) H (c <*> inv b)).
      apply (subgroup_mem_r _ (inv h2 <*> h1) H IsSubgroup).
      assumption.
    Qed.

    Lemma coset_reflexive: forall a (H : set G), is_subgroup H -> is_mem (right_coset H a) a.
    Proof.
      intros a H IsSubgroup.
      unfold right_coset, is_mem.
      rewrite inverse1.
      apply IsSubgroup.
    Qed.

    Theorem coset_representative:
      forall a b (H : set G),
        is_subgroup H -> right_coset H b a = true ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c.
    Proof.
      intros a b H IsSubgroup.
      intros Hb_a.
      (* going to show that a is in both Ha Hb *)
      remember (coset_reflexive a H IsSubgroup) as Ha_a.
      apply (coset_intersection a b H IsSubgroup); auto.
      exists a; auto.
    Qed.

    Theorem coset_mult: forall a b (H : set G),
        is_subgroup H -> is_mem H b -> is_mem (right_coset H a) (op b a).
      intros a b H IsSubgroup Hb_true.
      unfold right_coset, is_mem.
      autorewrite with core; auto.
    Qed.

    Theorem coset_zero: forall a (H: set G),
        is_subgroup H -> is_mem H a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H zero) c.
    Proof.
      intros a H IsSubgroup Ha_true.
      (* WTS: everything in Ha can be represented by something in H *)
      unfold right_coset.
      intros c.
      apply (subgroup_inverse _ _ IsSubgroup) in Ha_true.
      unfold is_mem.
      fold (is_mem H (c <*> inv a)).
      fold (is_mem H (c <*> inv a)).
      autorewrite with core.
      rewrite (subgroup_mem_r _ _ H IsSubgroup Ha_true).
      autorewrite with core.
      reflexivity.
    Qed.

  End cosets.

  Section normal_subgroups.

    Arguments is_mem {A} _ _.
    Arguments is_mem_dec {A} _ _.
    Arguments is_subgroup {G} _.
    Arguments right_coset {G} _.
    Arguments left_coset {G} _.

    Definition is_normal_subgroup (H: set G) :=
      is_subgroup H /\ forall (a h : G), is_mem H h -> is_mem H (a <*> h <*> inv a).

    Lemma normal_subgroup_intro: forall a h H,
        is_normal_subgroup H ->
        is_mem H h <-> is_mem H (a <*> h <*> inv a).
      intros a h H IsNormalSubgroup.
      destruct IsNormalSubgroup as [IsSubgroup Normality].
      split.
      intros h_Subgroup.
      apply Normality.
      assumption.
      intros h_conjugate.
      apply (Normality (inv a) _) in h_conjugate.
      autorewrite with core in h_conjugate.
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
      intros.
      rewrite <- (inverse_cancel a) at 2.
      apply (h_Membership (inv a)).
      assumption.
      intros; apply h_Membership; assumption.
    Qed.

    Theorem normal_subgroup_membership_commutes : forall a b (H : set G),
        is_normal_subgroup H -> is_mem H (a <*> b) <-> is_mem H (b <*> a).
      intros a b H IsNormalSubgroup.
      rewrite (normal_subgroup_intro (inv a) _).
      autorewrite with core.
      reflexivity.
      assumption.
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
      apply (subgroup_closed1 _ _ H IsSubgroup c_Coset) in d_Coset.
      rewrite group_assoc in d_Coset.
      rewrite <- (group_assoc c d _) in d_Coset.
      unfold is_mem in d_Coset.
      rewrite (normal_subgroup_membership_commutes (inv a) _ H IsNormalSubgroup) in d_Coset.
      rewrite inverse_apply.
      rewrite <- group_assoc.
      assumption.
    Qed.
  End normal_subgroups.

End groups.

Section homomorphisms.
  Definition is_homomorphism (A: Set) op inv zero (B: Set) op' inv' zero' (h: A -> B) :=
    is_group A op inv zero /\
    is_group B op' inv' zero' /\
    h zero = zero' /\
    forall a b,
      h (op a b) = op' (h a) (h b).

  Lemma id_homomorphism : forall A op inv zero,
      is_group A op inv zero -> is_homomorphism A op inv zero A op inv zero (fun a => a).
    intros A op inv zero.
    unfold is_homomorphism.
    intros IsGroup.
    auto.
  Qed.

  Lemma abelian_group_inv_homomorphism : forall A op inv zero,
    is_abelian_group A op inv zero ->
    is_homomorphism A op inv zero A op inv zero (fun a => (inv a)).
  Proof.
    intros A op inv zero.
    unfold is_abelian_group, is_commutative.
    intros [IsGroup IsCommutative].
    unfold is_homomorphism.
    split; [assumption | split; [assumption | split; [apply (inverse_zero A op inv zero IsGroup)|auto]]].
    intros a b.
    rewrite IsCommutative, (inverse_apply A op inv zero IsGroup). reflexivity.
  Qed.

  Variables (A B : Set)
            (op: A -> A -> A) (op': B -> B -> B)
            (inv: A -> A) (inv': B -> B)
            (zero : A) (zero' : B).

  Lemma homomorphism_inverse : forall h,
      is_homomorphism A op inv zero B op' inv' zero' h ->
      forall a, h (inv a) = inv' (h a).
    intros h.
    unfold is_homomorphism.
    intros [Group [Group' [Zero Homomorphism]]].
    intros a.
    apply (group_cancel_l B op' inv' zero' Group' (h a) _ _).
    rewrite <- Homomorphism.
    rewrite (inverse1 A op inv zero Group).
    rewrite (inverse1 B op' inv' zero' Group').
    assumption.
  Qed.

  Lemma homomorphism_assoc : forall h,
      is_homomorphism A op inv zero B op' inv' zero' h ->
      forall a b c, op' (h (op a b)) (h c) = op' (h a) (h (op b c)).
    intros h.
    unfold is_homomorphism.
    intros [Group [Group' [_ Homomorphism]]].
    intros a b c.
    rewrite Homomorphism.
    rewrite (group_assoc B op' inv' zero' Group').
    rewrite Homomorphism.
    reflexivity.
  Qed.

  (* NEXT: kernel of homomorphism is a normal subgroup, image of homomorphism is a subgroup *)
  (* a \in kern(f) if f(a) = z *)

  Definition is_kernel (h: A -> B) (k: A -> bool) :=
    is_homomorphism A op inv zero B op' inv' zero' h /\
    forall a, k a = true <-> (h a) = zero'.

  Definition is_image (h: A -> B) (i: B -> bool) :=
    is_homomorphism A op inv zero B op' inv' zero' h /\
    forall b, i b = true <-> exists a, (h a) = b.

  Lemma kernel_is_subgroup : forall h k,
    is_kernel h k -> is_subgroup A op inv zero k.
    intros h k.
    intros IsKernel.
    assert (is_kernel h k) as IsKernel2. assumption.
    destruct IsKernel2 as [[IsGroup [IsGroup' [HomomorphismZero Homomorphism]]] DefinitionOfKernel].
    unfold is_subgroup.
    split.
    apply DefinitionOfKernel; assumption.
    split.
    (* show kernel is closed under operation *)
    intros a b.
    rewrite (DefinitionOfKernel a), (DefinitionOfKernel b).
    intros [ha_zero hb_zero].
    apply DefinitionOfKernel.
    rewrite Homomorphism.
    rewrite ha_zero, hb_zero.
    rewrite (group_zero_l B op' inv' zero' IsGroup').
    reflexivity.
    (* show kernel is closed under inverse *)
    intros a.
    rewrite (DefinitionOfKernel a), (DefinitionOfKernel (inv a)).
    rewrite homomorphism_inverse.
    intros ha_zero.
    rewrite ha_zero.
    rewrite (inverse_zero B op' inv' zero' IsGroup').
    reflexivity.
    destruct IsKernel.
    auto.
  Qed.

  Lemma kernel_is_normal_subgroup: forall h k,
    is_kernel h k -> is_normal_subgroup A op inv zero k.
    intros h k IsKernel.
    unfold is_normal_subgroup.
    split; [apply (kernel_is_subgroup h k IsKernel) |auto].
    intros a b.
    unfold is_mem.
    intros b_kernel.
    destruct IsKernel as [IsHomomorphism DefinitionOfKernel].
    rewrite DefinitionOfKernel.
    assert (is_homomorphism A op inv zero B op' inv' zero' h) as IsHomomorphism2. auto.
    destruct IsHomomorphism2 as [Group [Group' [HomomorphismZero Homomorphism]]].
    repeat rewrite Homomorphism.
    apply DefinitionOfKernel in b_kernel.
    rewrite b_kernel.
    rewrite (group_zero_r B op' inv' zero' Group').
    rewrite (homomorphism_inverse h IsHomomorphism).
    rewrite (inverse1 B op' inv' zero' Group').
    reflexivity.
  Qed.

  Lemma image_is_subgroup : forall h i, is_image h i -> is_subgroup B op' inv' zero' i.
    intros h i.
    unfold is_image.
    intros [IsHomomorphism IsImage].
    unfold is_subgroup.
    split; [auto|split; [auto | auto]].
    (* show zero is in the image *)
    destruct IsHomomorphism as [Group [Group' [HomomorphismZero Homomorphism]]].
    apply (IsImage zero').
    exists zero.
    assumption.
    (* show closed under operation *)
    intros a b.
    rewrite (IsImage a), (IsImage b).
    intros [[a' a'_def] [b' b'_def]].
    apply IsImage.
    exists (op a' b').
    destruct IsHomomorphism as [_ [_ [_ Homomorphism]]].
    rewrite Homomorphism.
    rewrite a'_def, b'_def; reflexivity.
    (* show closed under inverse *)
    intros a.
    rewrite (IsImage a).
    intros [a' a'_def].
    apply IsImage.
    exists (inv a').
    rewrite (homomorphism_inverse h IsHomomorphism).
    rewrite a'_def.
    reflexivity.
  Qed.
End homomorphisms.

Section quotient_groups.

  Inductive Coset (A : Set) (H: A -> bool) :=
  | CosetRepresentative (a : A) : Coset A H.

  Definition quotient (A : Set) op inv zero (H : A -> bool)
             (IsNormalSubgroup: is_normal_subgroup A op inv zero H) :=
    (fun a => CosetRepresentative A H a).


  (* must define quotient zero, quotient op, quotient inverse *)

  Definition quotient_zero (A : Set) (H: A -> bool) zero := CosetRepresentative A H zero.

  Definition quotient_op (A : Set) (H: A -> bool) (op : A -> A -> A) : (Coset A H -> Coset A H -> Coset A H).
    intros a b.
    destruct a as [a].
    destruct b as [b].
    exact (CosetRepresentative A H (op a b)).
  Defined.

  Definition quotient_inv (A : Set) (H: A -> bool) (inv: A -> A): (Coset A H -> Coset A H).
    intros a.
    destruct a as [a].
    exact (CosetRepresentative A H (inv a)).
  Defined.

  Definition quotient_mapping (A: Set) (H: A -> bool) := fun a => CosetRepresentative A H a.

  Theorem quotient_is_group :
    forall A op inv zero H,
      is_group A op inv zero ->
      is_normal_subgroup A op inv zero H ->
      is_group (Coset A H)
               (quotient_op A H op)
               (quotient_inv A H inv)
               (quotient_zero A H zero).
  Proof.
    intros A op inv zero H IsGroup IsNormalSubgroup.
    unfold is_group.
    split.
    unfold is_semigroup.
    split.
    (* prove associativity *)
    unfold is_assoc.
    intros a b c.
    unfold quotient_op.
    destruct a as [a], b as [b], c as [c].
    rewrite (group_assoc A op inv zero IsGroup).
    reflexivity.
    (* prove zero *)
    unfold is_zero.
    intros a.
    destruct a as [a].
    unfold quotient_zero.
    unfold quotient_op.
    rewrite (group_zero_r A op inv zero IsGroup), (group_zero_l A op inv zero IsGroup).
    auto.
    (* prove inverse *)
    unfold is_inverse.
    intros a.
    destruct a as [a].
    unfold quotient_zero, quotient_op, quotient_inv.
    rewrite (inverse1 A op inv zero IsGroup), (inverse2 A op inv zero IsGroup).
    auto.
  Qed.

  Theorem quotient_is_homomorphism :
    forall A op inv zero H,
      is_group A op inv zero ->
      is_normal_subgroup A op inv zero H ->
      is_homomorphism A op inv zero (Coset A H)
                      (quotient_op A H op)
                      (quotient_inv A H inv)
                      (quotient_zero A H zero)
                      (quotient_mapping A H).
    intros A op inv zero H IsGroup IsNormalSubgroup.
    unfold is_homomorphism.
    split; [assumption | split; [apply quotient_is_group; assumption|auto]].
  Qed.


  Definition repr (A : Set) (H : A -> bool) (a : Coset A H) : A.
    destruct a; exact a.
  Defined.

  Definition coset_equivalence_relation (A : Set) (H : A -> bool) (op : A -> A -> A) (inv : A -> A) (zero : A)
             (a b : Coset A H) :=
    is_group A op inv zero ->
    is_normal_subgroup A op inv zero H ->
    is_mem A (left_coset A op inv (repr A H a) H) (repr A H b).

  Instance Coset_Equivalence (A : Set) (H: A -> bool) (op: A -> A -> A) (inv: A -> A) (zero: A):
    Equivalence (coset_equivalence_relation A H op inv zero).
  Proof.
    unfold coset_equivalence_relation, is_mem, left_coset.
    split.
    (* show reflexivity *)
    intros x IsGroup IsNormalSubgroup; simpl.
    rewrite (inverse2 A op inv zero IsGroup); apply IsNormalSubgroup.
    (* show symmetry *)
    intros x y; destruct x as [x], y as [y].
    intros x_y.
    intros IsGroup IsNormalSubgroup; simpl.
    remember (x_y IsGroup IsNormalSubgroup) as Q; destruct HeqQ; simpl in Q. (* ??? *)
(*    rewrite (normal_subgroup_membership_commutes A op inv zero IsGroup _ _ H IsNormalSubgroup) in Q.*)
    fold (is_mem A H (op (inv y) x)).
    rewrite <- (subgroup_inverse A op inv zero IsGroup _ H).
    rewrite (inverse_apply A op inv zero IsGroup).
    rewrite (inverse_cancel A op inv zero IsGroup).
    auto.
    destruct IsNormalSubgroup; auto.
    (* show transitivitity *)
    intros x y z; destruct x as [x], y as [y], z as [z].
    intros x_y y_z.
    intros IsGroup IsNormalSubgroup; simpl.
    simpl in x_y, y_z.
    remember (x_y IsGroup IsNormalSubgroup) as Q; destruct HeqQ; simpl in Q.
    remember (y_z IsGroup IsNormalSubgroup) as Q'; destruct HeqQ'; simpl in Q'.
    destruct IsNormalSubgroup as [IsSubgroup _].
    apply (subgroup_closed1 A op inv zero _ _ H IsSubgroup Q) in Q'.
    rewrite (group_assoc A op inv zero IsGroup) in Q'.
    rewrite <- (group_assoc A op inv zero IsGroup y _ _) in Q'.
    rewrite (inverse1 A op inv zero IsGroup) in Q'.
    rewrite (group_zero_l A op inv zero IsGroup) in Q'.
    assumption.
  Qed.

  Definition is_injective (A: Set) (B: Set) (h: A -> B) (H : B -> bool) :=
    forall a b, H (h a) = true /\ H (h b) = true -> (h a) = (h b) <-> a = b.

  Definition is_surjective (A: Set) (B: Set) (h: A -> B) (H : B -> bool) :=
    forall (b : B), is_mem H b <-> exists (a : A), h a = b.

  (* basically this is trivial because the definition of image / surjective are the same *)
  Theorem quotient_mapping_is_surjective_to_image:
    forall A op inv zero H I,
      is_image A (Coset A H)
                op (quotient_op A H op)
                inv (quotient_inv A H inv)
                zero (quotient_zero A H zero)
                (quotient_mapping A H) I ->
      is_surjective A (Coset A H) (quotient_mapping A H) I.
  Proof.
    intros A op inv zero H I IsImage.
    intros b; apply IsImage.
  Qed.

  Definition canonical_isomorphism (A B: Set) (H : A -> bool) (h : A -> B) (a : Coset A H) : B.
    destruct a as [a].
    exact (h a).
  Defined.

  Lemma canonical_isomorphism_is_homomorphism:
    forall A op inv zero B op' inv' zero' h K,
      is_group A op inv zero ->
      is_group B op' inv' zero' ->
      is_kernel A B op op' inv inv' zero zero' h K ->
      is_homomorphism
        (Coset A K) (quotient_op A K op) (quotient_inv A K inv) (quotient_zero A K zero)
        B op' inv' zero'
        (canonical_isomorphism A B K h).
  Proof.
    intros A op inv zero B op' inv' zero' h K.
    intros IsGroup IsGroup' IsKernel.
    unfold is_homomorphism.
    split.
    apply quotient_is_group.
    exact IsGroup.
    apply (kernel_is_normal_subgroup A B op op' inv inv' zero zero' h K).
    exact IsKernel.
    split; [exact IsGroup' | auto].
    split.
    unfold canonical_isomorphism.
    unfold quotient_zero.
    destruct IsKernel as [IsHomomorphism]; apply IsHomomorphism.
    intros a b.
    unfold canonical_isomorphism, quotient_op.
    destruct a as [a], b as [b].
    destruct IsKernel as [IsHomomorphism _]; apply IsHomomorphism.
  Qed.

  Definition coset_equivalence_relation' (A : Set) op inv (H : A -> bool) :=
    forall a b, CosetRepresentative A H a = CosetRepresentative A H b <->
                is_mem A (left_coset A op inv a H) b.

  (* FIRST ISOMORPHISM THEOREM *)
  Theorem quotient_of_homomorphism_is_isomorphic_to_image :
    forall A op inv zero B op' inv' zero' h K I,
      is_group A op inv zero ->
      is_group B op' inv' zero' ->
      coset_equivalence_relation' A op inv K ->
      is_kernel A B op op' inv inv' zero zero' h K ->
      is_image A B op op' inv inv' zero zero' h I ->
      (* the quotient group is isomorphic to the image of the homomorphism.
         we take the canonical isomorphism defined above and show that it is:
         (1) a homomorphism (proven above)
         (2) it is injective (coset equivalence relation is required)
         (3) it is surjective
       *)
      is_homomorphism
        (Coset A K) (quotient_op A K op) (quotient_inv A K inv) (quotient_zero A K zero)
        B op' inv' zero'
        (canonical_isomorphism A B K h) /\
      is_injective (Coset A K) B (canonical_isomorphism A B K h) I /\
      is_surjective (Coset A K) B (canonical_isomorphism A B K h) I.
  Proof.
    intros A op inv zero B op' inv' zero' h K I.
    intros IsGroup IsGroup' CosetEquivalenceRelation IsKernel IsImage.
    assert (is_homomorphism A op inv zero B op' inv' zero' h) as IsHomomorphism2. destruct IsImage; auto.
    split.
    apply canonical_isomorphism_is_homomorphism; [assumption|assumption|auto].
    split.
    (* show injectivity *)
    unfold is_injective.
    intros a b.
    destruct a as [a], b as [b].
    unfold canonical_isomorphism.
    destruct IsImage as [IsHomomorphism IsImage].
    repeat rewrite IsImage.
    intros [[a' a'_def] [b' b'_def]].
    split.
    intros ha_eq_hb.
    apply CosetEquivalenceRelation.
    unfold is_mem, left_coset.
    (*apply (group_add_l B op' (inv' (h a)) _ _) in ha_eq_hb.*)
    apply IsKernel.
    destruct IsHomomorphism2 as [_ [_ [_ Homomorphism]]].
    rewrite Homomorphism.
    apply (group_add_l B op' (inv' (h a)) _ _) in ha_eq_hb.
    rewrite (inverse2 B op' inv' zero' IsGroup') in ha_eq_hb.
    symmetry in ha_eq_hb.
    rewrite (homomorphism_inverse A B op op' inv inv' zero zero' h).
    assumption.
    assumption.
    intros cosets_equal.
    apply CosetEquivalenceRelation in cosets_equal.
    unfold is_mem, left_coset in cosets_equal.
    apply IsKernel in cosets_equal.
    apply (group_cancel_l B op' inv' zero' IsGroup' (inv' (h a))).
    rewrite (inverse2 B op' inv' zero' IsGroup').
    symmetry.
    destruct IsHomomorphism2 as [_ [_ [_ Homomorphism]]].
    rewrite Homomorphism in cosets_equal.
    rewrite <- (homomorphism_inverse A B op op' inv inv' zero zero' h IsHomomorphism).
    assumption.
    (* injectivity shown \o/ *)
    (* must show surjectivity now *)
    unfold is_surjective.
    intros b.
    split.
    intros b_Image.
    apply IsImage in b_Image.
    destruct b_Image as [a a_def].
    exists (CosetRepresentative A K a).
    unfold canonical_isomorphism.
    assumption.
    intros a_Coset.
    destruct a_Coset as [a a_isomorphism].
    unfold canonical_isomorphism in a_isomorphism.
    apply IsImage.
    destruct a as [a].
    exists a.
    assumption.
  Qed.

End quotient_groups.

Section group_examples.
  Require Import Coq.ZArith.BinInt.
  Require Import ZArithRing.
  Local Open Scope Z_scope.

  Lemma integers_with_addition_are_group : (is_group Z Z.add (fun n => - n)) Z.zero.
    unfold is_group.
    split.
    unfold is_semigroup.
    unfold is_assoc, is_zero.
    split.
    intros; ring.
    intros; split.
    rewrite Z.add_0_r; reflexivity.
    rewrite Z.add_0_l; reflexivity.
    unfold is_inverse.
    intros a.
    split.
    rewrite Z.add_opp_diag_r.
    reflexivity.
    rewrite Z.add_comm, Z.add_opp_diag_r.
    reflexivity.
  Qed.



Check Coset.
