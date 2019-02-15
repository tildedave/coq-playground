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

  Definition abelian_group (G: Group) := is_commutative (A G) (op G).

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

  Hint Rewrite inverse1.
  Hint Rewrite inverse2.
  Hint Rewrite inverse3.
  Hint Rewrite inverse4.

  Hint Rewrite group_zero_r.
  Hint Rewrite group_zero_l.
  Hint Rewrite group_assoc.

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

  End group_examples.

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
        is_subgroup H -> is_mem (right_coset H b) a ->
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
      intros; rewrite (normal_subgroup_intro (inv a) _).
      autorewrite with core.
      reflexivity.
      assumption.
    Qed.

    Theorem normal_subgroup_left_coset_iff_right_coset : forall a (H : set G),
        is_normal_subgroup H ->
        forall c, is_mem (left_coset a H) c <-> is_mem (right_coset H a) c.
    Proof.
      intros; apply normal_subgroup_membership_commutes.
      assumption.
    Qed.

    Lemma normal_subgroups_are_subgroups : forall (H : set G),
        is_normal_subgroup H -> is_subgroup H.
    Proof.
      unfold is_normal_subgroup; intros H IsNormalSubgroup.
      destruct IsNormalSubgroup; assumption.
    Qed.

    Lemma coset_mem : forall a c (H : set G),
        is_mem (right_coset H a) c <-> is_mem H (c <*> inv a).
    Proof.
      intros a c H.
      unfold right_coset, is_mem.
      reflexivity.
    Qed.

    Theorem normal_subgroup_coset_op : forall a b c d (H : set G),
        is_normal_subgroup H ->
        is_mem (right_coset H a) c ->
        is_mem (right_coset H b) d ->
        is_mem (right_coset H (a <*> b)) (c <*> d).
    Proof.
      intros a b c d H IsNormalSubgroup.
      assert (is_subgroup H) as IsSubgroup.  destruct IsNormalSubgroup; auto.
      intros c_Coset d_Coset.
(*      fold (is_mem H (c <*> d <*> inv (a <*> b))).      *)
      rewrite coset_mem in c_Coset, d_Coset.
      rewrite normal_subgroup_membership_commutes in c_Coset.
      apply coset_mem.
      apply (subgroup_closed1 _ _ H IsSubgroup c_Coset) in d_Coset.
      rewrite (normal_subgroup_intro a) in d_Coset.
      autorewrite with core in d_Coset.
      rewrite group_assoc, inverse_apply.
      assumption.
      assumption.
      assumption.
    Qed.
  End normal_subgroups.

End groups.

Hint Rewrite inverse1.
Hint Rewrite inverse2.
Hint Rewrite inverse3.
Hint Rewrite inverse4.

Hint Rewrite group_zero_r.
Hint Rewrite group_zero_l.
Hint Rewrite group_assoc.

Hint Rewrite inverse_cancel.
Hint Rewrite inverse_zero.
Hint Rewrite inverse_apply.

Section homomorphisms.
  Definition is_homomorphism (G1 : Group) (G2: Group) (h: G1 -> G2) :=
    h (zero G1) = (zero G2) /\
    forall a b,
      h ((op G1) a b) = (op G2) (h a) (h b).

  Lemma id_homomorphism : forall (G : Group), is_homomorphism G G (fun a => a).
  Proof.
    intros.
    unfold is_homomorphism.
    auto.
  Qed.

  Lemma abelian_group_inv_homomorphism : forall (G : Group),
    abelian_group G -> is_homomorphism G G (fun a => (inv G a)).
  Proof.
    intros G.
    unfold abelian_group, is_commutative.
    intros IsCommutative.
    unfold is_homomorphism.
    split; [apply inverse_zero | auto].
    intros a b.
    rewrite <- inverse_apply, (IsCommutative _ _).
    reflexivity.
  Qed.

  Lemma homomorphism : forall (G1 G2 : Group) (h : G1 -> G2),
      is_homomorphism G1 G2 h -> forall a b, h (op G1 a b) = op G2 (h a) (h b).
    intros G1 G2 h Homomorphism; apply Homomorphism.
  Qed.

  Lemma homomorphism_zero : forall (G1 G2 : Group) h,
      is_homomorphism G1 G2 h -> h (zero G1) = zero G2.
    intros G1 G2 h Homomorphism; apply Homomorphism.
  Qed.

  Lemma homomorphism_inverse : forall (G1 G2 : Group) h,
      is_homomorphism G1 G2 h -> forall a, h (inv G1 a) = inv G2 (h a).
    intros G1 G2 h [Zero Homomorphism] a.
    apply (group_cancel_l G2 (h a) _ _).
    rewrite <- Homomorphism.
    rewrite (inverse1 G1), (inverse1 G2).
    assumption.
  Qed.

  Lemma homomorphism_assoc : forall (G1 G2: Group) h,
      is_homomorphism G1 G2 h ->
      forall a b c, op G2 (h (op G1 a b)) (h c) = op G2 (h a) (h (op G1 b c)).
    intros G1 G2 h [Zero Homomorphism] a b c.
    rewrite Homomorphism, (group_assoc G2), Homomorphism.
    reflexivity.
  Qed.

  (* NEXT: kernel of homomorphism is a normal subgroup, image of homomorphism is a subgroup *)
  (* a \in kern(f) if f(a) = z *)

  Definition is_kernel (G1 G2: Group) (h: G1 -> G2) (K: set (A G1)) :=
    is_homomorphism G1 G2 h /\ forall a, is_mem _ K a <-> (h a) = (zero G2).

  Definition is_image (G1 G2: Group) (h: G1 -> G2) (I: set (A G2)) :=
    is_homomorphism G1 G2 h /\ forall b, is_mem _ I b <-> exists a, (h a) = b.

  Lemma kernel_is_subgroup : forall (G1 G2: Group) H K,
    is_kernel G1 G2 H K -> is_subgroup G1 K.
    intros G1 G2 H K [IsHomomorphism IsKernel].
    unfold is_subgroup.
    split.
    (* show zero mapped to zero *)
    apply IsKernel, IsHomomorphism.
    (* show kernel is closed under operation *)
    split.
    intros a b.
    rewrite (IsKernel a), (IsKernel b).
    intros [Ha_zero Hb_zero].
    apply IsKernel.
    destruct IsHomomorphism as [_ Homomorphism].
    rewrite Homomorphism.
    rewrite Ha_zero, Hb_zero.
    autorewrite with core; reflexivity.
    (* show kernel is closed under inverse *)
    intros a.
    rewrite (IsKernel a), (IsKernel (inv _ a)), homomorphism_inverse.
    intros ha_zero.
    rewrite ha_zero.
    autorewrite with core.
    reflexivity.
    assumption.
  Qed.

  Lemma kernel_is_normal_subgroup: forall (G1 G2 : Group) h K,
    is_kernel G1 G2 h K -> is_normal_subgroup _ K.
    intros G1 G2 h K IsKernel.
    unfold is_normal_subgroup.
    split; [apply (kernel_is_subgroup _ _ h K); assumption | auto].
    destruct IsKernel as [IsHomomorphism IsKernel].
    intros a b b_kernel.
    apply IsKernel.
    apply IsKernel in b_kernel.
    assert (is_homomorphism G1 G2 h) as IsHomomorphism2. assumption.
    destruct IsHomomorphism2 as [Zero Homomorphism].
    repeat rewrite Homomorphism.
    rewrite b_kernel.
    autorewrite with core.
    rewrite homomorphism_inverse.
    autorewrite with core.
    reflexivity.
    assumption.
  Qed.

  Lemma image_is_subgroup : forall (G1 G2: Group) h I,
      is_image G1 G2 h I -> is_subgroup _ I.
    intros G1 G2 h I.
    unfold is_image.
    intros [IsHomomorphism IsImage].
    unfold is_subgroup.
    split; [auto|split; [auto | auto]].
    (* show zero is in the image *)
    destruct IsHomomorphism as [Zero Homomorphism].
    apply (IsImage (zero _)).
    exists (zero _).
    assumption.
    (* show closed under operation *)
    intros a b.
    rewrite (IsImage a), (IsImage b).
    intros [[a' a'_def] [b' b'_def]].
    apply IsImage.
    exists (op G1 a' b').
    destruct IsHomomorphism as [Zero Homomorphism].
    rewrite Homomorphism.
    rewrite a'_def, b'_def; reflexivity.
    (* show closed under inverse *)
    intros a.
    rewrite (IsImage a).
    intros [a' a'_def].
    apply IsImage.
    exists (inv G1 a').
    rewrite homomorphism_inverse.
    rewrite a'_def.
    reflexivity.
    assumption.
  Qed.
End homomorphisms.

Section quotient_groups.

  (* represent coset equivalence how?
     well, I can definitely prove equivalence relationship for
     left_coset, right cosets, etc. *)

  Arguments right_coset {G} _ _.

  Inductive coset (G : Group) (H: set G) :=
  | coset_repr (a : G) : coset G H.

  Arguments coset_repr {G} _ _.
  Arguments coset {G} _.
  Arguments is_mem {A}.

  (* not sure how to do this without an axiom *)
  Axiom coset_right : forall (G : Group) (H: set G) a b,
      is_mem (right_coset H b) a -> coset_repr H a = coset_repr H b.

  Definition quotient_mapping (G : Group) (H : set G) :=
    (fun a => coset_repr H a).

  (* must define quotient zero, quotient op, quotient inverse *)

  Definition quotient_zero (G : Group) (H: set G) := coset_repr H (zero G).

  Definition quotient_op (G : Group) (H: set G) :
    coset H -> coset H -> coset H.
    intros a b.
    (* this is dumb,but basically we just don't care about the coset repr *)
    destruct a as [a].
    destruct b as [b].
    exact (coset_repr H ((op G) a b)).
  Defined.

  Definition quotient_inv (G : Group) (H: set G): coset H -> coset H.
    intros a.
    destruct a as [a].
    exact (coset_repr H ((inv G) a)).
  Defined.

  Arguments quotient_mapping {G} _.
  Arguments quotient_inv {G} _.
  Arguments quotient_op {G} _.
  Arguments quotient_zero {G} _.

  Definition quotient_group (G: Group) (H: set G) : Group.
    apply (makeGroup (coset H)
                     (quotient_op H)
                     (quotient_inv H)
                     (quotient_zero H)).
    (* show quotient op associative *)
    intros [a] [b] [c].
    unfold quotient_op; autorewrite with core; reflexivity.
    (* show quotient zero *)
    intros [a].
    unfold quotient_op, quotient_zero; autorewrite with core; auto.
    intros [a].
    unfold quotient_op, quotient_inv, quotient_zero; autorewrite with core.
    auto.
  Defined.

  Theorem quotient_is_homomorphism :
    forall (G : Group) (H : set G),
      is_homomorphism G (quotient_group G H) (quotient_mapping H).
  Proof.
    intros; unfold is_homomorphism; auto.
  Qed.

  Definition is_injective (A: Set) (B: Set) (h: A -> B) (H : set B) :=
    forall a b, is_mem H (h a) /\ is_mem H (h b) -> (h a) = (h b) <-> a = b.

  Definition is_surjective (A: Set) (B: Set) (h: A -> B) (H : set B) :=
    forall (b : B), is_mem H b <-> exists (a : A), h a = b.

  (* basically this is trivial because the definition of image / surjective are the same *)
  Theorem quotient_mapping_is_surjective_to_image:
    forall (G : Group) (H : set G) I,
      is_image G (quotient_group G H) (quotient_mapping H) I ->
      is_surjective G (quotient_group G H) (quotient_mapping H) I.
  Proof.
    intros G H I IsImage.
    unfold is_surjective.
    intros b; apply IsImage.
  Qed.

  Definition canonical_isomorphism (G1 G2: Group) (H : set G1) (h : G1 -> G2)
             (a : coset H) : G2.
    destruct a as [a].
    exact (h a).
  Defined.

  Lemma canonical_isomorphism_is_homomorphism :
    forall (G1 G2 : Group) (h : G1 -> G2) (K : set G1),
      is_homomorphism G1 G2 h ->
      is_kernel G1 G2 h K ->
      is_homomorphism (quotient_group G1 K) G2
                      (canonical_isomorphism G1 G2 K h).
  Proof.
    intros G1 G2 h K IsHomomorphism IsKernel.
    unfold is_homomorphism.
    split.
    (* zero maps to zero *)
    simpl; apply IsHomomorphism.
    intros [a] [b].
    apply IsHomomorphism.
  Qed.

  Hint Rewrite inverse1.

  (* FIRST ISOMORPHISM THEOREM *)
  Theorem quotient_of_homomorphism_is_isomorphic_to_image :
    forall (G1 G2 : Group) (h : G1 -> G2) (K : set G1) (I : set G2),
      is_homomorphism G1 G2 h ->
      is_kernel G1 G2 h K ->
      is_image G1 G2 h I ->
      (* homomorphism, injective, and surjective *)
      let h' := (canonical_isomorphism G1 G2 K h) in
      is_homomorphism (quotient_group G1 K) G2 h' /\
      is_injective (quotient_group G1 K) G2 h' I /\
      is_surjective (quotient_group G1 K) G2 h' I.
  Proof.
    intros G1 G2 h K I IsHomomorphism IsKernel IsImage.
    split.
    apply canonical_isomorphism_is_homomorphism; assumption.
    split.
    (* show injectivity *)
    unfold is_injective.
    intros [a] [b] [a_image b_image].
    unfold canonical_isomorphism.
    (* idea is that since a / b are mapped to the same thing, they're in the
       same coset of the quotient with the kernel *)
    split.
    intro H.
    apply (coset_right _ _ a b), IsKernel, (group_cancel_r _ (h b) _ _).
    rewrite (homomorphism _ _ _ IsHomomorphism).
    rewrite (homomorphism_inverse _ _ _ IsHomomorphism).
    autorewrite with core.
    assumption.
    intros H; inversion H; reflexivity.
    (* show surjectivity *)
    unfold is_surjective.
    intros b.
    split.
    intros ImageB.
    apply IsImage in ImageB.
    destruct ImageB as [b' b'_def].
    exists (coset_repr _ b').
    simpl; assumption.
    unfold canonical_isomorphism.
    intros Coset.
    destruct Coset as [[a']].
    apply IsImage.
    exists a'; assumption.
  Qed.

End quotient_groups.
