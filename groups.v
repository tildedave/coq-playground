Require Import Coq.Bool.Bool.
Require Import Setoid.
Require Import Coq.Classes.Equivalence.

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

    Structure subgroup (G : Group) : Type := makeSubgroup
    {
      subgroup_mem :> set G;
      subgroup_zero : is_mem subgroup_mem zero;
      subgroup_closed :
        forall a b, is_mem subgroup_mem a /\ is_mem subgroup_mem b -> is_mem subgroup_mem (a <*> b);
      subgroup_inverse :
        forall a, is_mem subgroup_mem a -> is_mem subgroup_mem (inv a)
    }.

  (* subgroup_mem is a characteristic function.
     TODO: figure out how to do this nicer ;)
   *)
    Definition is_subgroup (G : Group) (H: subgroup G) :=
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

    Lemma subgroup_closed1: forall (H: subgroup G) (a b : G),
        is_mem H a -> is_mem H b -> is_mem H (a <*> b).
    Proof.
      intros; apply subgroup_closed; auto.
    Qed.

    Lemma subgroup_closed2: forall (H : subgroup G) (a b : G),
        is_mem H a -> is_mem H b -> is_mem H (b <*> a).
    Proof.
      intros; apply subgroup_closed; auto.
    Qed.

    Lemma subgroup_inverse1: forall (H: subgroup G) (a : G),
        is_mem H a -> is_mem H (inv a).
      intros; apply subgroup_inverse; auto.
    Qed.

    Lemma subgroup_inverse2: forall (H: subgroup G) (a : G),
        is_mem H (inv a) -> is_mem H a.
      intros H a.
      intros.
      rewrite <- (inverse_cancel a).
      apply subgroup_inverse; assumption.
    Qed.

    Lemma subgroup_inverse3: forall (H: subgroup G) (a : G),
        is_mem H (inv a) <-> is_mem H a.
    Proof.
      intros.
      split; [apply subgroup_inverse2 | apply subgroup_inverse1].
    Qed.

    Lemma subgroup_op_non_member_right: forall (H: subgroup G) (a b : G),
        is_mem H a -> ~is_mem H b -> ~is_mem H (a <*> b).
      intros H a b Ha_mem Hb_not_mem.
      (* Suppose ab were in the subgroup.  Then a^{-1} ab would be in the subgroup, so b is in the subgroup.
         contradiction *)
      destruct (is_mem_dec _ H (a <*> b)) as [Hab_mem | Hab_not_mem].
      apply (subgroup_closed1 _ (inv a) _) in Hab_mem.
      autorewrite with core in Hab_mem; auto.
      apply subgroup_inverse; assumption.
      assumption.
    Qed.

    Lemma subgroup_op_non_member_left: forall (H : subgroup G) (a b : G),
        is_mem H b -> ~is_mem H a -> ~is_mem H (a <*> b).
      intros H a b Hb_mem Ha_not_mem.
      (* not sure if there is a clever way to use right, so we just duplicate the logic above (for now) *)
      (* Suppose ab were in the subgroup.  Then a^{-1} ab would be in the subgroup, so b is in the subgroup.
         contradiction *)
      destruct (is_mem_dec _ H (a <*> b)) as [Hab_mem | Hab_not_mem].
      apply (subgroup_closed1 _ _ (inv b)) in Hab_mem.
      autorewrite with core in Hab_mem; auto.
      apply subgroup_inverse; assumption.
      assumption.
    Qed.

    Lemma subgroup_mem_l:
      forall (H : subgroup G) a b,
        is_mem H a -> is_mem H (a <*> b) <-> is_mem H b.
      intros H a b Ha_mem.
      (* want to reason like .... is_mem H b
       If is_mem H a, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (is_mem_dec _ H b) as [Hb_mem | Hb_not_mem].
      remember (subgroup_closed1 _ _ _ Ha_mem Hb_mem).
      split; [intros; assumption | intros; assumption].
      (* a is member, b not member, so these are proofs by contradiction *)
      remember (subgroup_op_non_member_right _ a b Ha_mem Hb_not_mem) as Hab_not_mem.
      split.
      intros Hab_mem.
      contradict (is_mem_contradict _ _ _ Hab_mem Hab_not_mem).
      intros Hb_mem.
      contradict (is_mem_contradict _ _ _ Hb_mem Hb_not_mem).
    Qed.

    Lemma subgroup_mem_r: forall (H : subgroup G) a b,
        is_mem H b -> is_mem H (a <*> b) <-> is_mem H a.
      intros H a b Hb_mem.
      (* want to reason like .... is_mem H b
       If is_mem H a, then obviously since a is in the subgroup.
       If H a = false, then...
       *)
      destruct (is_mem_dec _ H a) as [Ha_mem | Ha_not_mem].
      remember (subgroup_closed1 _ _ _ Ha_mem Hb_mem).
      split; [intros; assumption | intros; assumption].
      (* a is member, b not member, so these are proofs by contradiction *)
      remember (subgroup_op_non_member_left _ a b Hb_mem Ha_not_mem) as Hab_not_mem.
      split.
      intros Hab_mem.
      contradict (is_mem_contradict _ _ _ Hab_mem Hab_not_mem).
      intros Ha_mem.
      contradict (is_mem_contradict _ _ _ Ha_mem Ha_not_mem).
    Qed.

    Lemma subgroup_inverse_non_member1: forall (H: subgroup G) a,
        ~is_mem H a -> ~is_mem H (inv a).
      intros H a.
      destruct (is_mem_dec _ H (inv a)) as [Ha_inv_true | Ha_inv_false].
      apply subgroup_inverse in Ha_inv_true.
      rewrite inverse_cancel in Ha_inv_true.
      intro Ha_false.
      contradict (is_mem_contradict _ _ _ Ha_inv_true Ha_false).
      intros; auto.
    Qed.

    Lemma subgroup_inverse_non_member2: forall (H: subgroup G) a,
        ~is_mem H (inv a) -> ~is_mem H a.
      intros H a.
      intros Ha_inv_false.
      apply (subgroup_inverse_non_member1 _ (inv a)) in Ha_inv_false.
      rewrite <- (inverse_cancel a).
      assumption.
    Qed.

  End subgroups.

  Section cosets.

    (* c \in aH if b \in H such that ab = c, b = a^{-1}c *)
    Definition left_coset (G: Group) (a : G) (H: subgroup G) : set G :=
      fun c => (subgroup_mem G H) ((inv a) <*> c).

    (* c \in Ha if b \in H such that ba = c, b = c a^{-1} *)
    Definition right_coset (G: Group) (H: subgroup G) (a: G) : set G :=
      fun c => (subgroup_mem G H) (c <*> (inv a)).

    Arguments is_mem {A} _ _.
    Arguments is_subgroup {G} _.
    Arguments right_coset {G} _.
    Arguments left_coset {G} _.

    Check right_coset.

    Lemma coset_intersection_helper_1:
      forall a b (H: subgroup G),
        (exists x, is_mem (right_coset H a) x /\  is_mem (right_coset H b) x) ->
        exists h1 h2, is_mem H h1 /\ is_mem H h2 /\ a = op (op (inv h1) h2) b.
      intros a b H [x [Ha_x Hb_x]].
      unfold right_coset, left_coset in Ha_x, Hb_x.
      exists (x <*> inv a), (x <*> inv b).
      split; [assumption | split; [assumption | auto]].
      rewrite inverse_apply.
      autorewrite with core; reflexivity.
    Qed.

    (* a in Hb -> Ha = Hb *)
    Lemma coset_intersection:
      forall a b (H: subgroup G),
        (exists x, is_mem (right_coset H a) x /\ is_mem (right_coset H b) x) ->
        (forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c).
      intros a b H Intersection.
      apply (coset_intersection_helper_1 a b H) in Intersection.
      destruct Intersection as [h1 [h2 [h1_Subgroup [h2_Subgroup a_definition]]]].
      intros c.
      unfold right_coset.
      rewrite a_definition.
      repeat rewrite inverse_apply.
      rewrite inverse_cancel.
      rewrite <- group_assoc.
      apply (subgroup_inverse1 _ h2) in h2_Subgroup.
      apply (subgroup_closed1 _ (inv h2) h1 h2_Subgroup) in h1_Subgroup.
      (* must get rid of the coset definitions in order to apply
         subgroup_mem_r *)
      unfold is_mem.
      rewrite group_assoc.
      rewrite <- (group_assoc c _ _).
      fold (@is_mem (A G) H (c <*> (inv b <*> inv h2 <*> h1))).
      fold (@is_mem (A G) H (c <*> inv b)).
      apply (subgroup_mem_r _ _ (inv h2 <*> h1)).
      assumption.
    Qed.

    Lemma coset_reflexive: forall a (H: subgroup G),
        is_mem (right_coset H a) a.
    Proof.
      intros a H.
      unfold right_coset, is_mem.
      rewrite inverse1.
      apply subgroup_zero.
    Qed.

    Theorem coset_representative:
      forall a b (H: subgroup G),
        is_mem (right_coset H b) a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c.
    Proof.
      intros a b H IsSubgroup.
      intros Hb_a.
      (* going to show that a is in both Ha Hb *)
      remember (coset_reflexive a H) as Ha_a.
      apply (coset_intersection a b _); auto.
      exists a; auto.
    Qed.

    Theorem coset_mult: forall a b (H: subgroup G),
        is_mem H b -> is_mem (right_coset H a) (op b a).
      intros a b H Hb_true.
      unfold right_coset, is_mem.
      autorewrite with core; auto.
    Qed.

    Theorem coset_zero: forall a (H: subgroup G),
        is_mem H a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H zero) c.
    Proof.
      intros a H Ha_true.
      (* WTS: everything in Ha can be represented by something in H *)
      unfold right_coset.
      intros c.
      apply subgroup_inverse in Ha_true.
      unfold is_mem.
      fold (is_mem H (c <*> inv a)).
      fold (is_mem H (c <*> inv a)).
      autorewrite with core.
      rewrite (subgroup_mem_r _ _ _ Ha_true).
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

    Structure normal_subgroup (G : Group) := makeNormalSubgroup
      {
        normal_subgroup_mem :> subgroup G ;
        normal_subgroup_conjugation: forall (a h : G), is_mem normal_subgroup_mem h -> is_mem normal_subgroup_mem (a <*> h <*> inv a)
      }.

    Arguments normal_subgroup_conjugation {G} _.

    Lemma normal_subgroup_intro: forall a h (H : normal_subgroup G),
        is_mem H h <-> is_mem H (a <*> h <*> inv a).
    Proof.
      intros a h H.
      split.
      intros h_Subgroup.
      apply normal_subgroup_conjugation.
      assumption.
      intros h_conjugate.
      apply (normal_subgroup_conjugation _ (inv a)) in h_conjugate.
      autorewrite with core in h_conjugate.
      assumption.
    Qed.

    Lemma normal_subgroup_conj_rewrite: forall a h (H : normal_subgroup G),
        is_mem H h ->
        is_mem H (a <*> h <*> inv a) <-> is_mem H ((inv a) <*> h <*> a).
    Proof.
      intros a h H h_Subgroup.
      (* inv (a b) = inv b inv a *)
      split.
      intros.
      rewrite <- (inverse_cancel a) at 2.
      apply (normal_subgroup_conjugation _ (inv a)).
      assumption.
      intros; apply normal_subgroup_conjugation; assumption.
    Qed.

    Theorem normal_subgroup_membership_commutes : forall a b (H: normal_subgroup G),
        is_mem H (a <*> b) <-> is_mem H (b <*> a).
      intros; rewrite (normal_subgroup_intro (inv a) _).
      autorewrite with core.
      reflexivity.
    Qed.

    Theorem normal_subgroup_left_coset_iff_right_coset : forall a (H: normal_subgroup G),
        forall c, is_mem (left_coset a H) c <-> is_mem (right_coset H a) c.
    Proof.
      intros; apply normal_subgroup_membership_commutes.
    Qed.

    Lemma coset_mem : forall a c (H: subgroup G),
        is_mem (right_coset H a) c <-> is_mem H (c <*> inv a).
    Proof.
      intros a c H.
      unfold right_coset, is_mem.
      reflexivity.
    Qed.

    Theorem normal_subgroup_coset_op : forall a b c d (H: normal_subgroup G),
        is_mem (right_coset H a) c ->
        is_mem (right_coset H b) d ->
        is_mem (right_coset H (a <*> b)) (c <*> d).
    Proof.
      intros a b c d H.
      intros c_Coset d_Coset.
      rewrite coset_mem in c_Coset, d_Coset.
      rewrite normal_subgroup_membership_commutes in c_Coset.
      apply coset_mem.
      apply (subgroup_closed1 _ _ _ c_Coset) in d_Coset.
      rewrite (normal_subgroup_intro a) in d_Coset.
      autorewrite with core in d_Coset.
      rewrite group_assoc, inverse_apply.
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
  Structure homomorphism (G1 G2: Group) := makeHomomorphism
    {
      h :> G1 -> G2 ;
      homomorphism_zero : h (zero G1) = (zero G2) ;
      homomorphism_apply : forall a b, h ((op G1) a b) = (op G2) (h a) (h b)
    }.

  Definition id_homomorphism : forall (G : Group), (homomorphism G G).
    intros G.
    apply (makeHomomorphism G G (fun a => a)).
    reflexivity.
    reflexivity.
  Defined.

  Lemma abelian_group_inv_homomorphism : forall (G : Group),
    abelian_group G -> homomorphism G G.
  Proof.
    intros G.
    unfold abelian_group, is_commutative.
    intros IsCommutative.
    apply (makeHomomorphism G G (fun a => inv _ a)).
    apply inverse_zero.
    intros a b.
    rewrite <- inverse_apply, (IsCommutative _ _).
    reflexivity.
  Qed.

  Lemma homomorphism_inverse : forall (G1 G2: Group) (h: homomorphism G1 G2),
      forall a, h (inv G1 a) = inv G2 (h a).
  Proof.
    intros G1 G2 h a.
    apply (group_cancel_l G2 (h a)).
    rewrite <- homomorphism_apply, (inverse1 G1), (inverse1 G2).
    apply homomorphism_zero.
  Qed.

  Lemma homomorphism_assoc : forall (G1 G2: Group) (h: homomorphism G1 G2),
      forall a b c, op G2 (h (op G1 a b)) (h c) = op G2 (h a) (h (op G1 b c)).
    intros G1 G2 h a b c.
    rewrite homomorphism_apply, (group_assoc G2), homomorphism_apply.
    reflexivity.
  Qed.

  (* NEXT: kernel of homomorphism is a normal subgroup, image of homomorphism is a subgroup *)
  (* a \in kern(f) if f(a) = z *)

  Structure kernel G1 G2 (h: homomorphism G1 G2) :=
    {
      K :> set (A G1);
      kernel_mem : forall a, is_mem _ K a <-> (h a) = (zero G2)
    }.

  Structure image G1 G2 (h: homomorphism G1 G2) :=
    {
      I :> set (A G2);
      image_mem : forall b, is_mem _ I b <-> exists a, (h a) = b
    }.

  Arguments kernel_mem {G1} {G2} _ _.
  Arguments image_mem {G1} {G2} _ _.

  Lemma kernel_subgroup : forall (G1 G2: Group) h (K : kernel G1 G2 h),
      subgroup G1.
  Proof.
    intros G1 G2 h K.
    apply (makeSubgroup _ K).
    (* show zero mapped to zero *)
    apply kernel_mem, homomorphism_zero.
    (* show kernel is closed under operation *)
    intros a b.
    rewrite (kernel_mem h K a), (kernel_mem h K b).
    intros [Ha_zero Hb_zero].
    apply kernel_mem.
    rewrite homomorphism_apply, Ha_zero, Hb_zero.
    autorewrite with core; reflexivity.
    (* show kernel is closed under inverse *)
    intros a.
    rewrite (kernel_mem h K a), (kernel_mem h K (inv _ a)), homomorphism_inverse.
    intros ha_zero.
    rewrite ha_zero.
    autorewrite with core.
    reflexivity.
  Defined.

  Lemma kernel_normal_subgroup:
    forall G1 G2 h (K : kernel G1 G2 h), normal_subgroup G1.
  Proof.
    intros G1 G2 h K.
    apply (makeNormalSubgroup _ (kernel_subgroup _ _ _ K)).
    intros a b b_kernel.
    apply kernel_mem.
    apply kernel_mem in b_kernel.
    repeat rewrite homomorphism_apply.
    rewrite b_kernel.
    autorewrite with core.
    rewrite homomorphism_inverse.
    autorewrite with core.
    reflexivity.
  Defined.

  Lemma image_subgroup : forall G1 G2 h (I: image G1 G2 h), subgroup G2.
    intros G1 G2 h I.
    apply (makeSubgroup _ I).
    (* show zero is in the image *)
    apply (image_mem _ _ (zero _)).
    exists (zero _).
    apply homomorphism_zero.
    (* show closed under operation *)
    intros a b.
    rewrite (image_mem _ _ a), (image_mem _ _ b).
    intros [[a' a'_def] [b' b'_def]].
    apply image_mem.
    exists (op G1 a' b').
    rewrite homomorphism_apply, a'_def, b'_def; reflexivity.
    (* show closed under inverse *)
    intros a.
    rewrite (image_mem _ _ a).
    intros [a' a'_def].
    apply image_mem.
    exists (inv G1 a').
    rewrite homomorphism_inverse, a'_def.
    reflexivity.
  Defined.
End homomorphisms.

Section quotient_groups.
  (* represent coset equivalence how?
     well, I can definitely prove equivalence relationship for
     left_coset, right cosets, etc. *)

  Arguments kernel_subgroup {G1} {G2} {h}.
  Arguments kernel_normal_subgroup {G1} {G2} {h}.
  Arguments image_subgroup {G1} {G2} {h}.

  Arguments right_coset {G} _ _.

  Structure coset (G: Group) (H: subgroup G) : Type := makeCoset
    {
      repr :> G ;
    }.

  Arguments is_mem {A}.

  Definition quotient_mapping (G: Group) (H: subgroup G) (a: G) : coset G H.
    apply (makeCoset _ _ a).
  Defined.

  Check quotient_mapping.

  (* must define quotient zero, quotient op, quotient inverse *)

  Definition quotient_zero G H : coset G H.
    apply (makeCoset _ _ (zero G)).
  Defined.

  Definition quotient_op G H : coset G H -> coset G H -> coset G H.
    intros a b.
    (* this is dumb,but basically we just don't care about the coset repr *)
    destruct a as [a].
    destruct b as [b].
    exact (makeCoset _ _ ((op G) a b)).
  Defined.

  Definition quotient_inv G H: coset G H -> coset G H.
    intros a.
    destruct a as [a].
    exact (makeCoset _ _ ((inv G) a)).
  Defined.

  Arguments quotient_mapping {G} _.
  Arguments quotient_inv {G} _.
  Arguments quotient_op {G} _.
  Arguments quotient_zero {G} _.

  Definition quotient_group (G: Group) (H: subgroup G) : Group.
    apply (makeGroup (coset G H)
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

  Theorem quotient_homomorphism :
    forall (G : Group) (H: subgroup G),
      homomorphism G (quotient_group G H).
  Proof.
    intros.
    (* quotient_mapping is map from group to coset group *)
    remember (quotient_mapping H) as h.
    unfold quotient_mapping in Heqh.
    (* must show it is a homomorphism *)
    apply (makeHomomorphism _ (quotient_group G H) h).
    rewrite Heqh; auto.
    intros; rewrite Heqh; auto.
  Qed.

  (* Old definitions, require term rewriting.  I think in Coq terms per type
     are unique - need to understand if there's some way to define a structure
     that comes with a rewriting rule on it. *)

  Definition is_injective' (A: Set) (B: Set) (h: A -> B) (H : set B) :=
    forall a b, is_mem H (h a) /\ is_mem H (h b) -> (h a) = (h b) <-> a = b.

  Definition is_surjective' (A: Set) (B: Set) (h: A -> B) (H : set B) :=
    forall (b : B), is_mem H b <-> exists (a : A), h a = b.

  (* New definitions, I can prove things with these, but they lock in the
     concept of mapping explicitly to cosets, so the statement of the first iso
     theorem is less general *)
  Check Equivalence.

  Definition coset_repr G H (a : coset G H) : G.
    destruct a as [a].
    exact a.
  Defined.

  Arguments coset_repr {G} {H} _.

  (* a and b are equivalent if there is some c that *)

  Definition coset_equivalence (G: Group) H (a b: coset G H) :=
    exists c,
      is_mem (right_coset H c) (coset_repr a) /\
      is_mem (right_coset H c) (coset_repr b).

  Instance Coset_Equivalence G H: Equivalence (coset_equivalence G H).
  Proof.
    unfold coset_equivalence, coset_repr.
    split.
    unfold Reflexive; intros x.
    exists (coset_repr x).
    split; [apply coset_reflexive | apply coset_reflexive].
    unfold Symmetric; intros x y [c [x_c y_c]].
    exists c.
    split; [auto|auto].
    unfold Transitive; intros x y z.
    intros [c1 [x_c1 y_c1]] [c2 [y_c2 z_c2]].
    (* this is easy but annoying *)
  Admitted.

  Arguments coset_equivalence {G} {H}.

  Check coset_equivalence.

  Definition is_injective_equiv (G1 G2: Group) (h: G1 -> G2)
             (equiv: G1 -> G1 -> Prop) :=
      forall a b,
        h a = h b -> (* a and b in same coset *)
        equiv a b.

  Definition is_surjective (G1 G2: Group) (h: G1 -> G2) H :=
    forall b, is_mem H b <-> exists a, h a = b.

  (* basically this is trivial because the definition of image / surjective are the same *)
  Theorem quotient_mapping_is_surjective_to_image:
    forall G H (I: image G _ (quotient_homomorphism G H)),
      is_surjective _ _ (quotient_homomorphism G H) I.
  Proof.
    intros G H I b.
    apply image_mem.
  Qed.

  Definition canonical_mapping G1 G2 h (K: kernel G1 G2 h)
             (a : quotient_group G1 (kernel_subgroup K)) : G2.
    destruct a as [a].
    exact (h a).
  Defined.

  Definition canonical_isomorphism :
    forall G1 G2 h (K : kernel G1 G2 h),
      homomorphism (quotient_group G1 (kernel_subgroup K)) G2.
  Proof.
    intros G1 G2 h K.
    apply (makeHomomorphism _ _ (canonical_mapping G1 G2 h K)).
    simpl; apply homomorphism_zero.
    intros [a] [b].
    apply homomorphism_apply.
  Defined.

  (* if canonical isomorphism maps two members to the same element of G2, they
     are in the same coset of K *)

  Lemma homomorphism_right_coset:
    forall G1 G2 h (K: kernel G1 G2 h),
      forall (a b: G1),
      h a = h b -> is_mem (right_coset (kernel_subgroup K) a) b.
    intros G1 G2 h K.
    intros a b ha_eq_b.
    unfold right_coset, is_mem; simpl.
    apply kernel_mem.
    rewrite homomorphism_apply, <- ha_eq_b.
    rewrite <- homomorphism_apply.
    autorewrite with core.
    apply homomorphism_zero.
  Qed.

  Lemma canonical_isomorphism_rewrite:
    forall G1 G2 h (K: kernel G1 G2 h) a b,
      (canonical_isomorphism G1 G2 h K) {| repr := a |} =
      (canonical_isomorphism G1 G2 h K) {| repr := b |} ->
      let K_Subgroup := kernel_subgroup K in
      is_mem (right_coset K_Subgroup a) b.
  Proof.
    intros G1 G2 h K a b.
    simpl.
    apply homomorphism_right_coset.
  Qed.

  (* coset equivalence relation solves this, but obviously the coset
     equivalence relation could be trivial and just say everything is
     equivalent to everything. what prevents this?
     do we need to make sure all our statements are true up to equivalence?
     (seems like I should prove that the homomorphism restricts to the
     equivalence relation.) *)

  Lemma canonical_isomorphism_restricted :
    forall G1 G2 h (K: kernel G1 G2 h),
      let h' := (canonical_isomorphism G1 G2 h K) in
      forall a b,
      h' a = h' b <-> coset_equivalence a b.
  Proof.
    intros G1 G2 h K.
    simpl.
    intros a b.
    unfold canonical_mapping.
    destruct a as [a].
    destruct b as [b].
    unfold coset_equivalence.
    split.
    intros ha_eq_hb.
    apply (homomorphism_right_coset _ _ _ K) in ha_eq_hb.
    exists a.
    split; [apply coset_reflexive | auto].
    (* feels like all of this can be done by the rewriting system :| *)
    intros [c [c_in_a c_in_b]].
    unfold is_mem, right_coset in c_in_a, c_in_b.
    simpl in c_in_a, c_in_b.
    apply kernel_mem in c_in_a.
    apply kernel_mem in c_in_b.
    rewrite homomorphism_apply in c_in_a, c_in_b.
    rewrite homomorphism_inverse in c_in_a.
    rewrite homomorphism_inverse in c_in_b.
    apply (group_add_r _ (h c)) in c_in_a.
    apply (group_add_r _ (h c)) in c_in_b.
    autorewrite with core in c_in_a.
    autorewrite with core in c_in_b.
    rewrite c_in_a, c_in_b.
    reflexivity.
  Qed.

  Definition quotient_group_repr G K (a : quotient_group G K) : coset G K.
    destruct a as [a].
    exact (makeCoset _ _ a).
  Defined.

  Arguments quotient_group_repr {G} {K}.

  Definition quotient_group_equivalence G K (a b: quotient_group G K) : Prop.
    exact (coset_equivalence (quotient_group_repr a) (quotient_group_repr b)).
  Defined.

  Arguments quotient_group_equivalence {G} {K} _ _.

  Lemma canonical_isomorphism_injectivity : forall G1 G2 h K,
      let iso := canonical_isomorphism G1 G2 h K in
      forall a b,
      iso a = iso b -> quotient_group_equivalence a b.
  Proof.
    intros G1 G2 h K.
    intros iso a b.
    destruct a as [a].
    destruct b as [b].
    intros H.
    apply canonical_isomorphism_rewrite in H.
    unfold quotient_group_equivalence, coset_equivalence.
    simpl.
    exists a.
    split; [apply coset_reflexive | assumption].
  Qed.

  (* FIRST ISOMORPHISM THEOREM *)
  Theorem quotient_of_homomorphism_is_isomorphic_to_image :
    forall G1 G2 h (K: kernel G1 G2 h) (I: image G1 G2 h),
      (* homomorphism, injective, and surjective *)
      let h' := (canonical_isomorphism G1 G2 h K) in
      let I_Subgroup := image_subgroup I in
      let K_Subgroup := kernel_subgroup K in
      is_injective_equiv (quotient_group G1 K_Subgroup) G2 h'
                         quotient_group_equivalence /\
      is_surjective (quotient_group G1 K_Subgroup) G2 h' I.
  Proof.
    intros G1 G2 h K I.
    split.
    (* show injectivity *)
    unfold is_injective_equiv.
    apply canonical_isomorphism_injectivity.
    (* show surjectivity *)
    unfold is_surjective.
    intros b.
    split.
    intros ImageB.
    apply image_mem in ImageB.
    destruct ImageB as [b' b'_def].
    exists (makeCoset _ _ b').
    simpl; assumption.
    simpl.
    intros Coset.
    destruct Coset as [[a']].
    apply image_mem.
    exists a'; assumption.
  Qed.
End quotient_groups.
