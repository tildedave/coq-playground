Require Import Coq.Bool.Bool.
Require Import Setoid.
Require Import Coq.Classes.Equivalence.
Require Import List.
Require Import ListSet.
Require Import ListUtils.

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
      z : A ;

      op_assoc : forall a b c, op a (op b c) = op (op a b) c;
      op_z : forall a, op a z = a /\ op z a = a ;
      op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
    }.

  Definition abelian_group (G: Group) := is_commutative (A G) (op G).

  Arguments z {g}.
  Arguments op {g} _ _.
  Arguments inv {g} _.

  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Variable (G : Group).

  Lemma inverse1 : forall (a : G), a <*> (inv a) = z.
    apply op_inverse.
  Qed.

  Lemma inverse2 : forall (a: G), (inv a) <*> a = z.
    apply op_inverse.
  Qed.

  Lemma inverse3 : forall (a b : G), inv a <*> (a <*> b) = b.
    intros.
    rewrite op_assoc, inverse2.
    apply op_z.
  Qed.

  Lemma inverse4 : forall (a b : G), a <*> (inv a <*> b) = b.
    intros.
    rewrite op_assoc, inverse1.
    apply op_z.
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

  Lemma group_z_r: forall (a : G), a <*> z = a.
    apply op_z.
  Qed.

  Lemma group_z_l: forall (a : G), z <*> a = a.
    apply op_z.
  Qed.

  Lemma group_assoc: forall (a b c : G), (a <*> b) <*> c = a <*> (b <*> c).
    intros; rewrite op_assoc; reflexivity.
  Qed.

  Lemma group_cancel_l: forall (a b c : G), a <*> b = a <*> c -> b = c.
    intros a b c OpABEqOpAC.
    rewrite <- (group_z_l b), <- (group_z_l c).
    rewrite <- (inverse2 a).
    repeat rewrite group_assoc.
    apply (group_add_l (inv a)).
    assumption.
  Qed.

  Lemma group_cancel_r: forall (a b c :G), b <*> a = c <*> a -> b = c.
    intros a b c OpABEqOpAC.
    rewrite <- (group_z_r b), <- (group_z_r c).
    rewrite <- (inverse1 a).
    repeat rewrite <- group_assoc.
    apply (group_add_r (inv a)).
    assumption.
  Qed.

  Theorem id_is_unique: forall a : G, (forall b : G, a <*> b = b) -> a = z.
    intros a ADef.
    apply (group_cancel_r (inv a)).
    rewrite group_z_l; apply ADef.
  Qed.

  Theorem op_z_commutes: forall (a b : G), a <*> b = z <-> b <*> a = z.
    intros a b.
    split.
    intro OpABZ.
    symmetry.
    apply (group_cancel_l a _ _), (group_cancel_l b _ _).
    rewrite <- group_assoc, <- (group_assoc a b a).
    rewrite OpABZ, group_z_r, group_z_l.
    reflexivity.
    intro OpBAZ.
    symmetry.
    apply (group_cancel_l b _ _), (group_cancel_l a _ _).
    rewrite <- group_assoc, <- (group_assoc b a b).
    rewrite OpBAZ, group_z_r, group_z_l.
    reflexivity.
  Qed.

  Theorem inverse_unique: forall (a b : G), a <*> b = z -> b = inv a.
    intros a b.
    intros OpABZ.
    apply (group_cancel_l a _ _).
    rewrite inverse1.
    assumption.
  Qed.

  Theorem inverse_cancel: forall (a : G), inv (inv a) = a.
    intros a.
    (* show (inv a) * a = z *)
    remember (inverse2 a) as H.
    destruct HeqH.
    apply inverse_unique in H.
    symmetry; assumption.
  Qed.

  Hint Rewrite inverse1.
  Hint Rewrite inverse2.
  Hint Rewrite inverse3.
  Hint Rewrite inverse4.

  Hint Rewrite group_z_r.
  Hint Rewrite group_z_l.
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

  Lemma inverse_z: @inv G z = z.
    apply (group_cancel_l z).
    rewrite inverse1, group_z_l.
    reflexivity.
  Qed.

  Hint Rewrite inverse_z.

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
      forall a, ~is_mem H a <-> (H a) = false.
      intros a.
      unfold is_mem.
      rewrite <- not_true_iff_false.
      reflexivity.
    Qed.

    Structure subgroup (G : Group) : Type := makeSubgroup
    {
      subgroup_mem :> set G;
      subgroup_z : is_mem subgroup_mem z;
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
      is_mem H z /\
      (* subgroup is closed under operation *)
      (forall a b, is_mem H a /\ is_mem H b -> is_mem H (a <*> b)) /\
      (* if an element is in the subgroup, its inverse is too *)
      forall a, is_mem H a -> is_mem H (inv a).

    Arguments is_subgroup {G} _.

    (* H is a subgroup *)
    (* H is inductively defined, z is in it,
       if a is in it, inv a is in it, if a b is in it, a op b is in it
       z is a consequence of the other two
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
      apply subgroup_z.
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

    Theorem coset_z: forall a (H: subgroup G),
        is_mem H a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H z) c.
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

Hint Rewrite group_z_r.
Hint Rewrite group_z_l.
Hint Rewrite group_assoc.

Hint Rewrite inverse_cancel.
Hint Rewrite inverse_z.
Hint Rewrite inverse_apply.

Section homomorphisms.

  Structure homomorphism (G1 G2: Group) := makeHomomorphism
    {
      h :> G1 -> G2 ;
      homomorphism_z : h (z G1) = (z G2) ;
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
    apply inverse_z.
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
    apply homomorphism_z.
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
      kernel_mem : forall a, is_mem _ K a <-> (h a) = (z G2)
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
    (* show z mapped to z *)
    apply kernel_mem, homomorphism_z.
    (* show kernel is closed under operation *)
    intros a b.
    rewrite (kernel_mem h K a), (kernel_mem h K b).
    intros [Ha_z Hb_z].
    apply kernel_mem.
    rewrite homomorphism_apply, Ha_z, Hb_z.
    autorewrite with core; reflexivity.
    (* show kernel is closed under inverse *)
    intros a.
    rewrite (kernel_mem h K a), (kernel_mem h K (inv _ a)), homomorphism_inverse.
    intros ha_z.
    rewrite ha_z.
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
    (* show z is in the image *)
    apply (image_mem _ _ (z _)).
    exists (z _).
    apply homomorphism_z.
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

  (* must define quotient z, quotient op, quotient inverse *)

  Definition quotient_z G H : coset G H.
    apply (makeCoset _ _ (z G)).
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
  Arguments quotient_z {G} _.

  Definition quotient_group (G: Group) (H: subgroup G) : Group.
    apply (makeGroup (coset G H)
                     (quotient_op H)
                     (quotient_inv H)
                     (quotient_z H)).
    (* show quotient op associative *)
    intros [a] [b] [c].
    unfold quotient_op; autorewrite with core; reflexivity.
    (* show quotient z *)
    intros [a].
    unfold quotient_op, quotient_z; autorewrite with core; auto.
    intros [a].
    unfold quotient_op, quotient_inv, quotient_z; autorewrite with core.
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

  Definition coset_with_repr G H (a : coset G H) : G.
    destruct a as [a].
    exact a.
  Defined.

  Arguments coset_with_repr {G} {H} _.

  (* a and b are equivalent if there is some c that *)

  Definition coset_equivalence (G: Group) (H: normal_subgroup G)
             (a b: coset G H) :=
    exists c,
      is_mem (right_coset H c) (coset_with_repr a) /\
      is_mem (right_coset H c) (coset_with_repr b).

  Instance Coset_Equivalence G H: Equivalence (coset_equivalence G H).
  Proof.
    unfold coset_equivalence, coset_with_repr.
    split.
    unfold Reflexive; intros x.
    exists (coset_with_repr x).
    split; [apply coset_reflexive | apply coset_reflexive].
    unfold Symmetric; intros x y [c [x_c y_c]].
    exists c.
    split; [auto|auto].
    unfold Transitive; intros x y z.
    destruct x as [x].
    destruct y as [y].
    destruct z as [z].
    intros [c1 [x_c1 y_c1]] [c2 [y_c2 z_c2]].
    (* this is easy but annoying *)
    (* there's some element such that x and y are in the same coset *)
    (* there's some element such that y and z are in the same coset *)
    (* so, some element witnesses x and z in the same coset through
       coset_intersection *)
    (*
      x_c1 : is_mem (right_coset H c1) x
      y_c1 : is_mem (right_coset H c1) y
      y_c2 : is_mem (right_coset H c2) y
      z_c2 : is_mem (right_coset H c2) z

      coset_representative
     : forall (G : Group) (a b : G) (H : subgroup G),
       is_mem (right_coset H b) a ->
       forall c : G, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c

     *)
    auto.
    exists c1.
    split; [assumption | auto].
    rewrite (coset_intersection G _ c2 H); [assumption | exists y; auto].
  Qed.

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
    simpl; apply homomorphism_z.
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
    apply homomorphism_z.
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
      forall (a b : coset G1 (kernel_subgroup K)),
      h' a = h' b <-> (@coset_equivalence G1 (kernel_normal_subgroup K)) a b.
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

  Definition quotient_group_equivalence G (K: normal_subgroup G) (a b: quotient_group G K) : Prop.
    exact (@coset_equivalence G K (quotient_group_repr a) (quotient_group_repr b)).
  Defined.

  Instance Quotient_Group_Equivalence G H: Equivalence (quotient_group_equivalence G H).
  Proof.
    unfold quotient_group_equivalence.
    (* figure out how to do this later *)
  Admitted.

  Arguments quotient_group_equivalence {G} {K} _ _.

  Lemma canonical_isomorphism_injectivity : forall G1 G2 h K,
      let iso := canonical_isomorphism G1 G2 h K in
      forall a b,
        iso a = iso b ->
        @quotient_group_equivalence G1 (kernel_normal_subgroup K) a b.
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
      let K_Subgroup := kernel_normal_subgroup K in
      is_injective_equiv (quotient_group G1 K_Subgroup) G2 h'
                         (@quotient_group_equivalence G1 K_Subgroup) /\
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

Section klein_4_group.
  Inductive klein :=
    k_I | k_X | k_Y | k_Z.

  Definition klein_op k1 k2 :=
    match (k1, k2) with
    | (k_I, _) => k2
    | (_, k_I) => k1
    | (k_X, k_X) => k_I
    | (k_X, k_Y) => k_Z
    | (k_X, k_Z) => k_Y
    | (k_Y, k_X) => k_Z
    | (k_Y, k_Y) => k_I
    | (k_Y, k_Z) => k_X
    | (k_Z, k_X) => k_Y
    | (k_Z, k_Y) => k_X
    | (k_Z, k_Z) => k_I
    end.

  Definition klein_inv (k1: klein) := k1.

  Lemma klein_z : forall k, klein_op k_I k = k.
    unfold klein_op.
    auto.
  Qed.

  Lemma klein_z2 : forall k, klein_op k k_I = k.
    intros.
    unfold klein_op.
    destruct k; [auto | auto | auto | auto].
  Qed.

  Lemma klein_abelian : forall x y, klein_op x y = klein_op y x.
    intros x y.
    destruct x.
    rewrite klein_z, klein_z2; reflexivity.
    destruct y; [auto | auto | auto | auto].
    destruct y; [auto | auto | auto | auto].
    destruct y; [auto | auto | auto | auto].
  Qed.

  Lemma klein_double : forall k, klein_op k k = k_I.
    simple destruct k; [split; auto | auto | auto | auto].
  Qed.

  Hint Rewrite klein_double.
  Hint Rewrite klein_z.
  Hint Rewrite klein_z2.

  Definition klein_group : Group.
    apply (makeGroup klein klein_op klein_inv k_I).
    Focus 2.
    destruct a; [split; auto | auto | auto | auto].
    Focus 2.
    intros; unfold klein_inv; rewrite klein_double; auto.
    (* associativity *)
    destruct a; destruct b; destruct c; compute; reflexivity.
  Defined.

End klein_4_group.

Require Import Coq.Logic.FinFun.

Section finite_groups.
  Import ListNotations.

  Structure finite_group := makeFiniteGroup
    {
      G :> Group;
      seq : list G;
      seq_listing : Listing seq;
    }.

  Structure finite_subgroup (G: Group) := makeFiniteSubgroup
    {
      H :> subgroup G;
      subgroup_seq : list G;
      subgroup_seq_in : forall g, is_mem _ H g <-> In g subgroup_seq;
      subgroup_seq_nodup : NoDup subgroup_seq;
    }.

  Definition cardinality (G: finite_group) :=
    length (seq G).

  Definition subgroup_filter (G: finite_group) (H: subgroup G) l : list G :=
    filter (fun a => (subgroup_mem _ H a)) l.

  Lemma subgroup_filter_NoDup (G: finite_group) H :
    forall l, NoDup l -> NoDup (subgroup_filter G H l).
  Proof.
    unfold subgroup_filter; intros; apply filter_NoDup; assumption.
  Qed.

  Lemma subgroup_filter_contains (G: finite_group) H :
    forall g, In g (subgroup_filter G H (seq G)) <-> is_mem _ H g.
  Proof.
    intros g.
    split.
    cut (forall l, In g (subgroup_filter G H l) -> is_mem G H g).
    intros Cut; apply Cut.
    (* prove cut *)
    induction l; simpl; auto.
    intros H1; contradict H1.
    destruct (is_mem_dec G H a).
    simpl.
    unfold is_mem in i.
    rewrite i.
    intros H1.
    apply in_inv in H1.
    destruct H1 as [a_is_g | g_in_subgroup].
    rewrite <- a_is_g; unfold is_mem; auto.
    apply IHl; assumption.
    unfold is_mem in n.
    apply not_true_is_false in n.
    rewrite n; apply IHl.
    (* prove being in the subgroup means it is in the filter of the seq *)
    cut (forall l, is_mem G H g -> In g l -> In g (subgroup_filter G H l)).
    intros Cut H_mem.
    remember (seq_listing G) as Q.
    destruct Q as [NoDup Full].
    apply (Cut (seq G) H_mem (Full g)).
    (* prove cut *)
    induction l; auto.
    intros H_mem In_g.
    simpl.
    destruct In_g as [g_is_a | g_in_l].
    unfold is_mem in H_mem.
    rewrite g_is_a, H_mem.
    apply in_eq.
    destruct (true_dec (subgroup_mem _ H a)).
    rewrite e; apply in_cons, IHl; assumption.
    rewrite e; apply IHl; assumption.
  Qed.

  (* take a subgroup, take a finite group, create a finite subgroup *)
  Definition subgroup_finite_group (G: finite_group) (H: subgroup G) : finite_subgroup G.
  Proof.
    apply (makeFiniteSubgroup _ H (subgroup_filter G H (seq G))).
    (* forall g : G, is_mem G H g <-> In g (subgroup_filter G H (seq G)) *)
    split; apply subgroup_filter_contains.
    apply subgroup_filter_NoDup, seq_listing.
  Qed.

  Definition cardinality_subgroup (G: finite_group) (H: subgroup G) : nat :=
    length (subgroup_filter G H (seq G)).

  Theorem klein_group_finite : finite_group.
    apply (makeFiniteGroup klein_group [k_I; k_X; k_Y; k_Z]).
    split.
    2: {
      unfold Full.
      destruct a; compute; auto.
    }
    apply NoDup_cons.
    apply not_in_cons.
    split ; [discriminate |auto].
    apply not_in_cons.
    split ; [discriminate |auto].
    apply not_in_cons.
    split ; [discriminate |auto].
    apply NoDup_cons.
    apply not_in_cons.
    split ; [discriminate |auto].
    apply not_in_cons.
    split ; [discriminate |auto].
    apply NoDup_cons.
    apply not_in_cons.
    split ; [discriminate |auto].
    apply NoDup_cons.
    auto; auto.
    apply NoDup_nil.
  Defined.

  Definition klein_eq_dec k1 k2 :=
    match k1 with
    | k_I => match k2 with k_I => true | _ => false end
    | k_X => match k2 with k_X => true | _ => false end
    | k_Y => match k2 with k_Y => true | _ => false end
    | k_Z  => match k2 with k_Z => true | _ => false end
    end.

  Definition klein_subgroup (k: klein_group) : subgroup klein_group.
    remember ((fun k' => match k' with
                           | k_I => true
                           | _ => klein_eq_dec k k'
                        end) : set klein_group) as char.
    apply (makeSubgroup _ char); auto.
    rewrite Heqchar; cbv; auto.
    (* closed under op *)
    destruct k in Heqchar; simple destruct a; simple destruct b;
      rewrite Heqchar; cbv; intros H; auto.
    (* closed under op: impossible cases *)
    0-36: destruct H; auto.
  Defined.

  Definition klein_subgroup_X := klein_subgroup k_X.
  Definition klein_subgroup_Y := klein_subgroup k_Y.
  Definition klein_subgroup_Z := klein_subgroup k_Z.

  Require Import Arith BinNat Nat.

  Lemma finite_subgroup_bounded (G: finite_group) (H : subgroup G):
    cardinality_subgroup G H <= cardinality G.
  Proof.
    remember (seq G) as S.
    unfold cardinality, cardinality_subgroup.
    assert (forall l, length (subgroup_filter G H l) <= length l) as H0.
    induction l; auto.
    unfold subgroup_filter.
    simpl.
    destruct (subgroup_mem _ H a).
    apply le_n_S; auto.
    apply le_S; auto.
    (* proved, so we can just apply this *)
    apply H0.
  Qed.

  Lemma z_in_seq_G (G: finite_group) : In (z G) (seq G).
  Proof.
    apply seq_listing.
  Qed.

  Lemma in_subgroup_seq_is_mem (G: finite_group) (H: finite_subgroup G) :
    forall c, In c (subgroup_seq _ H) <-> is_mem _ H c.
  Proof.
    intros c.
    split; apply subgroup_seq_in.
  Qed.

  Lemma inv_cancel G: forall a b, inv G a = inv G b -> a = b.
  Proof.
    intros b c inv_equal.
    apply (group_add_l _ b) in inv_equal.
    apply (group_add_r _ c) in inv_equal.
    autorewrite with core in inv_equal; auto.
  Qed.

  Hint Rewrite inv_cancel.

  Theorem subgroup_injective (G: finite_group) (H: finite_subgroup G) a:
    Injective (fun c => op G c (inv G a)).
  Proof.
    unfold Injective.
    intros x y H0; apply (group_add_r _ a _) in H0.
    autorewrite with core in H0; auto.
  Qed.

  (* To show Lagrange's Theorem we will use the map from a to its cosets.
     We will show it is surjective (so every coset shows up)
     Then we will show every coset has n members *)

  (* Must define a canonical coset map so we can say it's injective *)
  Definition coset_repr (G: finite_group) (H: subgroup G) g :=
    hd_error (filter (right_coset G H g) (seq G)).

  Lemma hd_error_nil: forall A (l: list A), hd_error l = None <-> l = [].
  Proof.
    intros A l.
    compute; destruct l; split; auto; intros H; contradict H; discriminate.
  Qed.

  Theorem coset_repr_always_some (G: finite_group) (H: subgroup G) :
    forall g, coset_repr G H g <> None.
  Proof.
    intros g.
    unfold not, coset_repr.
    rewrite hd_error_nil.
    destruct (seq_listing G) as [NoDup Full].
    intros filter_def.
    apply ((filter_empty _ _ _ filter_def g) (Full g)), coset_reflexive.
  Qed.

  Definition canonical_right_coset (G: finite_group) (H: subgroup G) g :=
    match coset_repr G H g with
    (* value should not matter because this branch will never be taken, just needs to check *)
    | None => g
    | Some a => a
    end.

  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_I).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_X).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_Y).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_Z).

  Definition finite_coset (G: finite_group) (H: subgroup G) g :=
    (filter (right_coset G H g) (seq G)).

  Lemma finite_coset_NoDup (G: finite_group) (H: subgroup G) g :
    NoDup (finite_coset G H g).
  Proof.
    apply filter_NoDup, seq_listing.
  Qed.

  Arguments op {g} _ _.
  Arguments inv {g} _.
  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Lemma finite_coset_same_size_as_subgroup (G: finite_group) (H: finite_subgroup G):
    forall g, length (finite_coset G H g) = cardinality_subgroup G H.
  Proof.
    intros g.
    remember (fun c => c <*> (inv g)) as f.
    (* h \in H, take this to a coset of g *)
    (* every member of the coset of Hg = h * g = a *)
    remember (fun h => (h <*> g)) as f_inv.
    apply (NoDup_injection_length _ _ _ _ f f_inv).
    - apply finite_coset_NoDup.
    - apply subgroup_filter_NoDup; apply seq_listing.
      (* show f is injective *)
    - rewrite Heqf.
      intros x y Q'.
      apply (group_cancel_r _ (inv g)); auto.
    (* show f' is injective *)
    - rewrite Heqf_inv.
      intros x y Q'.
      apply (group_cancel_r _ g x y); auto.
    (* show cosets maps into subgroup *)
    - intros c.
      unfold finite_coset.
      unfold subgroup_filter.
      repeat rewrite filter_In.
      rewrite Heqf.
      unfold right_coset.
      repeat split; try apply seq_listing;destruct H0; auto.
    (* show subgroup maps back into the cosets *)
    - intros d.
      unfold finite_coset.
      unfold subgroup_filter.
      repeat rewrite filter_In.
      rewrite Heqf_inv.
      unfold right_coset.
      autorewrite with core.
      repeat split; try apply seq_listing; destruct H0; auto.
    (* functions are inverses of one another *)
    - intros x; rewrite Heqf, Heqf_inv.
      autorewrite with core.
      reflexivity.
  Qed.

  Definition group_eq_decidable (G: Group) := forall (x y : G), {x = y} + {x <> y}.

  Theorem klein_group_eq_decidable: group_eq_decidable klein_group.
  Proof.
    simple destruct x; simple destruct y; auto; right; discriminate.
  Defined.

  Definition unique_cosets (G: finite_group) (H: subgroup G) (group_eq_dec: group_eq_decidable G) :=
    fold_right
      (set_add group_eq_dec)
      (empty_set G)
      (map (canonical_right_coset G H) (seq G)).

  Inductive fn_partition (A: Type) (l: list A) (f: A -> list A) :=
  | fn_partition_intro:
      NoDup l ->
      (forall b x y, In b (f x) -> In b (f y) -> x = y) ->
      (forall x y, length (f x) = length (f y)) ->
      (forall a, NoDup (f a)) ->
      (forall a, exists b, In a (f b)) ->
      fn_partition A l f.

  Theorem unique_cosets_is_partition  (G: finite_group) (H: subgroup G) group_eq_dec:
    fn_partition G (unique_cosets G H group_eq_dec) (finite_coset G H).
  Proof.
    apply fn_partition_intro.
    - unfold unique_cosets.
  Admitted.

  Definition expand_partition (A: Type) (l: list A) (f: A -> list A) :=
    flat_map (fun (x : A) => map (fun y => pair x y) (f x)) l.

  Compute (let G := klein_group_finite in
          let H := klein_subgroup_X in
          let group_eq_dec := klein_group_eq_decidable in
          expand_partition G (unique_cosets G H group_eq_dec) (finite_coset G H)).

  Lemma in_not_append: forall (A: Type) (l1 l2: list A) a,
      ~ In a l1 -> ~ In a l2 -> ~ In a (l1 ++ l2).
  Proof.
    (* come back to this, this is straightforward *)
  Admitted.

  Lemma NoDup_append: forall (A: Type) (l1 l2: list A),
      NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
  Proof.
    intros A.
    induction l1; intros l2 l1_NoDup l2_NoDup NotInL2; simpl; auto.
    apply NoDup_cons; apply NoDup_cons_iff in l1_NoDup;
      destruct l1_NoDup;
      [ apply in_not_append, NotInL2 | apply IHl1 ]; simpl; auto.
    intros; apply NotInL2; apply in_cons; auto.
  Qed.

  (*   NoDup (concat (map (fun x : A => map (fun y : A => (x, y)) (f x)) l)) *)

  (* Issues: NoDup concat requires some judgement over the whole list of passed in lists
     (i.e. it is a partition). *)

  Lemma in_concat_map: forall (A B: Type) (f: A -> list B) b (l: list A),
      In b (concat (map f l)) -> exists a, In b (f a) /\ In a l.
  Proof.
    intros A B f b.
    induction l; simpl.
    - intros H; contradict H; auto.
    - intros In_b.
      apply in_app_or in In_b.
      destruct In_b as [b_in_f_a | b_in_rest];
        [exists a | apply IHl in b_in_rest; destruct b_in_rest as [d def_d]; exists d];
        tauto.
  Qed.

  Theorem expand_partition_NoDup (A: Type) (l: list A) (f: A -> list A) :
    fn_partition A l f -> NoDup (expand_partition A l f).
  Proof.
    intros [l_NoDup _ _ NoRepeat _].
    unfold expand_partition.
    rewrite flat_map_concat_map.
    remember (fun x : A => map (fun y : A => (x, y)) (f x)) as inj.

    induction l; simpl.
    apply NoDup_nil.
    apply NoDup_append.
    rewrite Heqinj; apply Injective_map_NoDup;
      [intros x y H; inversion H | apply NoRepeat]; auto.
    apply IHl.
    apply NoDup_cons_iff in l_NoDup; destruct l_NoDup; auto.
    intros q.
    destruct q as [x y].
    intros xy_a.
    intros InRest.
    apply in_concat_map in InRest.
    destruct InRest as [d d_in_rest].
    (* we will derive a = d which will contradict NoDup *)
    destruct d_in_rest as [xy_d d_in_rest].
    rewrite Heqinj, in_map_iff in xy_a.
    rewrite Heqinj, in_map_iff in xy_d.
    destruct xy_a as [r [a_def _]].
    destruct xy_d as [s [d_def _]].
    inversion a_def.
    inversion d_def.
    rewrite <- H3 in H1.
    rewrite H1 in l_NoDup.
    rewrite NoDup_cons_iff in l_NoDup.
    destruct l_NoDup; auto.
  Qed.

  Theorem expand_partition_listing (

  Theorem expand_partition_same_size (A: Set) (l: list A) (f: A -> list A) (f_inv: A -> A)
          (seq_A: list A):
    Listing seq_A ->
    fn_partition A l f ->
    (forall e, In (f_inv e) (f e)) ->
    length (expand_partition A l f) = length seq_A.
  Proof.
    intros Listing.
    intros [l_NoDup IsNonEmpty NoOverlap SameLength NoRepeat EveryElementInPartition].
    intros InverseWitness.
    apply (NoDup_injection_length _ _ _ _ snd (fun x => pair (f_inv x) x)).
    2: apply Listing.
    (* snd being injective is not straightforward.
       we need a way to say something more about the structure of the partitions... *)
    3: {
      unfold Injective.
      intros x y.
      intros eq.
      inversion eq.
      reflexivity.
    }
    5: auto.

    3: {
      intros c.
      unfold expand_partition.
      rewrite flat_map_concat_map.
      Search (In _ (concat _)).
      split; [intros; apply Listing | ];auto.
      intros H.
      apply in_concat_append.
      (* this is awful too *)
  Abort.

  (* so let's say we have this, can we prove the size? *)

  Theorem lagrange_theorem : forall (G: finite_group) (H: finite_subgroup G) group_eq_dec,
      length (unique_cosets G H group_eq_dec) * cardinality_subgroup G H =
      cardinality G.
  Proof.
    (* blah *)
  Admitted.

End finite_groups.
