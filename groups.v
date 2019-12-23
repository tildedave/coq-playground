Require Import Coq.Bool.Bool.
Require Import Setoid.
Require Import Coq.Classes.Equivalence.
Require Import List.
Require Import ListSet.
Require Import ListUtils.
Import ListNotations.

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
      op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z ;

      eq_dec: forall (x y : A), {x = y} + {x <> y}
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

  Theorem inverse_unique: forall (a b: G), a <*> b = z -> b = inv a.
    intros a b.
    intros OpABZ.
    apply (group_cancel_l a _ _).
    rewrite inverse1.
    assumption.
  Qed.

  Theorem inverse_cancel: forall (a: G), inv (inv a) = a.
    intros a.
    (* show (inv a) * a = z *)
    remember (inverse2 a) as H.
    destruct HeqH.
    apply inverse_unique in H.
    symmetry; assumption.
  Qed.

  Hint Rewrite inverse_cancel.

  Lemma inverse_cancel2: forall (a b: G), inv a = inv b -> a = b.
  Proof.
    intros b c inv_equal.
    rewrite <- inverse_cancel, <- inv_equal.
    autorewrite with core; reflexivity.
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
    Require Import Znumtheory.
    Require Import Zdiv.

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
      assert (forall a b : Z, {a = b} + {a <> b}) as eq_dec. apply Z.eq_dec.
      exact (makeGroup Z Z.add (fun n => - n) Z.zero Z_assoc Z_zero Z_inv eq_dec).
    Defined.

    Inductive lt_n (n : Z): Set :=
    | lt_n_intro (m : Z) : lt_n n.

    Definition lt_n_add n (a b: lt_n n) : (lt_n n).
      destruct a as [r]; induction b as [s].
      apply (lt_n_intro n ((r + s) mod n)); auto.
    Defined.

    Notation "m # n" := (lt_n_intro n m) (at level 50, left associativity).
    Check (4 # 3).

    Axiom lt_n_intro_equality:
      forall n a b, a mod n = b mod n -> a # n = b # n.

    Require Import Omega.

    Definition lt_n_inv n (a: lt_n n) : (lt_n n).
      destruct a as [r].
      apply (lt_n_intro n (-r)); auto.
    Defined.

    Definition lt_n_zero n := lt_n_intro n 0.

    Lemma lt_n_add_rewrite n: forall r s,
        lt_n_add n (r # n) (s # n) =
        ((r + s) mod n) # n.
    Proof.
      intros r s.
      simpl.
      reflexivity.
    Qed.

    Lemma lt_n_add_comm n:
      forall (a b : lt_n n), lt_n_add n a b = lt_n_add n b a.
    Proof.
      intros a b.
      case a; case b; intros r s.
      repeat rewrite lt_n_add_rewrite.
      rewrite Zplus_comm.
      reflexivity.
    Defined.

    Lemma lt_n_add_assoc n:
      forall (a b c: lt_n n),
        lt_n_add n (lt_n_add n a b) c = lt_n_add n a (lt_n_add n b c).
    Proof.
      intros a b c.
      case a; case b; case c; intros r s t.
      repeat rewrite lt_n_add_rewrite.
      rewrite Zplus_mod_idemp_l.
      rewrite <- Zplus_assoc.
      rewrite Zplus_mod.
      rewrite Zplus_mod_idemp_l.
      reflexivity.
    Qed.

    Lemma lt_n_add_inverse n: forall a,
        lt_n_add n a (lt_n_inv n a) =
        lt_n_zero n.
    Proof.
      intros.
      unfold lt_n_add.
      destruct a; simpl; rewrite Z.add_opp_diag_r, Zmod_0_l; reflexivity.
    Qed.

    Lemma lt_n_add_zero n: forall a,
        lt_n_add n a (lt_n_zero n) = a.
    Proof.
      intros; unfold lt_n_add.
      simpl.
      Search (_ + 0).
      destruct a.
      rewrite Z.add_0_r.
      apply lt_n_intro_equality.
      rewrite Zmod_mod.
      reflexivity.
    Qed.

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

    Lemma subgroup_mem_bool_rewrite (H: subgroup G):
      forall a b, (is_mem H a) <-> (is_mem H b) -> subgroup_mem G H a = subgroup_mem G H b.
    Proof.
      intros a b.
      unfold is_mem.
      destruct (subgroup_mem G H a); destruct (subgroup_mem G H b); try tauto; symmetry; tauto.
    Qed.

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
    Arguments right_coset {G} _.
    Arguments left_coset {G} _.

    Check right_coset.

    Lemma right_coset_mem_bool_rewrite (H: subgroup G):
      forall a b c, (is_mem (right_coset H a) c) <-> (is_mem (right_coset H b) c) ->
                    right_coset H a c = right_coset H b c.
    Proof.
      intros a b c.
      unfold is_mem.
      destruct (right_coset H a c); destruct (right_coset H b c); try tauto; symmetry; tauto.
    Qed.

    Lemma coset_subgroup: forall a b  (H: subgroup G),
        is_mem (right_coset H b) a <-> is_mem H (a <*> inv b).
    Proof.
      intros; unfold is_mem, right_coset.
      reflexivity.
    Qed.

    Lemma coset_swap: forall a b (H: subgroup G),
        is_mem (right_coset H b) a <-> is_mem (right_coset H a) b.
    Proof.
      intros; repeat rewrite coset_subgroup.
      rewrite <- subgroup_inverse3, inverse_apply.
      autorewrite with core.
      reflexivity.
    Qed.

    Lemma coset_trans: forall a b c (H: subgroup G),
        is_mem (right_coset H a) b -> is_mem (right_coset H b) c -> is_mem (right_coset H a) c.
    Proof.
      intros a b c H; repeat rewrite coset_subgroup.
      intros H_a H_b.
      replace (c <*> inv a) with ((c <*> inv b) <*> (b <*> inv a));
        [apply subgroup_closed | autorewrite with core]; auto.
    Qed.

    (* a in Hb -> Ha = Hb *)
    Lemma coset_intersection: forall a b d (H: subgroup G),
        is_mem (right_coset H a) d ->
        is_mem (right_coset H b) d ->
        (forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c).
    Proof.
      intros a b d H Coset_ad Coset_bd.
      assert (is_mem (right_coset H a) b) as Coset_ab.
      rewrite coset_swap in Coset_bd.
      apply (coset_trans _ d); auto.
      repeat rewrite (coset_swap c).
      split.
      - intros Coset_ac.
        rewrite coset_swap in Coset_ab; apply (coset_trans _ a); auto.
      - intros Coset_bc.
        apply (coset_trans _ b); auto.
    Qed.

    Lemma coset_reflexive: forall a (H: subgroup G),
        is_mem (right_coset H a) a.
    Proof.
      intros a H.
      rewrite coset_subgroup.
      autorewrite with core; apply subgroup_z.
    Qed.

    Theorem coset_representative:
      forall a b (H: subgroup G),
        is_mem (right_coset H b) a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H b) c.
    Proof.
      intros; split; apply coset_trans; [ | rewrite coset_swap ]; auto.
    Qed.

    Theorem coset_mult: forall a b (H: subgroup G),
        is_mem H b -> is_mem (right_coset H a) (b <*> a).
    Proof.
      intros a b H H_mem.
      rewrite coset_subgroup.
      autorewrite with core; auto.
    Qed.

    Theorem coset_z: forall a (H: subgroup G),
        is_mem H a ->
        forall c, is_mem (right_coset H a) c <-> is_mem (right_coset H z) c.
    Proof.
      intros a H Ha_true.
      intros c.
      repeat rewrite coset_subgroup.
      autorewrite with core.
      apply subgroup_mem_r, subgroup_inverse; auto.
    Qed.

  End cosets.

  Section normal_subgroups.

    Arguments is_mem {A} _ _.
    Arguments is_mem_dec {A} _ _.
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

  Definition quotient_eq_dec G H: forall a b : (coset G H), {a = b} + {a <> b}.
  Proof.
    intros a b.
    destruct a as [a].
    destruct b as [b].
    destruct (eq_dec G a b).
    left; rewrite e; auto.
    right; contradict n; inversion n; auto.
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
    apply quotient_eq_dec.
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
    rewrite (coset_intersection G c1 c2 y); auto.
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
    (* associativity *)
    - destruct a; destruct b; destruct c; compute; reflexivity.
    (* identity *)
    - destruct a; [split; auto | auto | auto | auto].
    (* inverse *)
    - intros; unfold klein_inv; rewrite klein_double; auto.
    - simple destruct x; simple destruct y; auto; right; discriminate.
  Defined.

End klein_4_group.

Require Import Coq.Logic.FinFun.

Section finite_groups.
  Import ListNotations.

  Arguments op {g} _ _.
  Arguments inv {g} _.
  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Structure finite_group := makeFiniteGroup
    {
      G :> Group;
      seq_g : list G;
      seq_listing : Listing seq_g;
    }.

  Structure finite_subgroup (G: Group) := makeFiniteSubgroup
    {
      H :> subgroup G;
      subgroup_seq : list G;
      subgroup_seq_in : forall g, is_mem _ H g <-> In g subgroup_seq;
      subgroup_seq_nodup : NoDup subgroup_seq;
    }.

  Definition cardinality (G: finite_group) :=
    length (seq_g G).

  Definition subgroup_filter (G: finite_group) (H: subgroup G) l : list G :=
    filter (fun a => (subgroup_mem _ H a)) l.

  Hint Immediate subgroup_filter.

  Lemma subgroup_filter_NoDup (G: finite_group) H :
    forall l, NoDup l -> NoDup (subgroup_filter G H l).
  Proof.
    unfold subgroup_filter; intros; apply filter_NoDup; assumption.
  Qed.

  Lemma subgroup_filter_contains (G: finite_group) H :
    forall g, In g (subgroup_filter G H (seq_g G)) <-> is_mem _ H g.
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
    apply (Cut (seq_g G) H_mem (Full g)).
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
    apply (makeFiniteSubgroup _ H (subgroup_filter G H (seq_g G))).
    (* forall g : G, is_mem G H g <-> In g (subgroup_filter G H (seq_g G)) *)
    split; apply subgroup_filter_contains.
    apply subgroup_filter_NoDup, seq_listing.
  Qed.

  Definition cardinality_subgroup (G: finite_group) (H: subgroup G) : nat :=
    length (subgroup_filter G H (seq_g G)).

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
    remember (seq_g G) as S.
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

  Lemma z_in_seq_G (G: finite_group) : In (z G) (seq_g G).
  Proof.
    apply seq_listing.
  Qed.

  Lemma in_subgroup_seq_is_mem (G: finite_group) (H: finite_subgroup G) :
    forall c, In c (subgroup_seq _ H) <-> is_mem _ H c.
  Proof.
    intros c.
    split; apply subgroup_seq_in.
  Qed.

  (* To show Lagrange's Theorem we will use the map from a to its cosets.
     We will show it is surjective (so every coset shows up)
     Then we will show every coset has n members *)

  (* Must define a canonical coset map so we can say it's injective *)
  Definition coset_repr (G: finite_group) (H: subgroup G) g :=
    hd_error (filter (right_coset G H g) (seq_g G)).

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

  (* everything that is a member of the coset has the same canonical_right_coset value *)
  Lemma coset_repr_mem (G: finite_group) (H: subgroup G) g :
    coset_repr G H g = Some g ->
    forall a, is_mem _ (right_coset G H g) a <-> coset_repr G H a = Some g.
  Proof.
    intros CosetReprG.
    intros a.
    split.
    - rewrite coset_subgroup.
      intros CosetMem.
      unfold coset_repr.
      apply hd_error_cons.
      unfold coset_repr in CosetReprG.
      apply hd_error_cons in CosetReprG.
      destruct CosetReprG as [l2 l2_def].
      exists l2.
      rewrite <- l2_def.
      apply filter_eq.
      intros b.
      unfold right_coset.
      apply subgroup_mem_bool_rewrite.
      split.
      + intros; replace (b <*> inv g) with ((b <*> inv a) <*> (a <*> inv g));
          [apply subgroup_closed; tauto | autorewrite with core; reflexivity].
      + intros.
        rewrite <- subgroup_inverse3, inverse_apply in CosetMem.
        autorewrite with core in CosetMem.
        replace (b <*> inv a) with ((b <*> inv g) <*> (g <*> inv a));
          [apply subgroup_closed | autorewrite with core]; auto.
    - intros CosetSame.
      unfold coset_repr in CosetSame.
      apply hd_error_cons in CosetSame.
      destruct CosetSame as [l2 l2_def].
      assert (In g (filter (right_coset G H a) (seq_g G))) as g_in_filter.
      rewrite l2_def; simpl; auto.
      rewrite filter_In in g_in_filter.
      rewrite coset_swap; destruct g_in_filter; tauto.
  Qed.

  Lemma coset_repr_always_mem (G: finite_group) (H: subgroup G):
    forall g d,
      coset_repr G H g = Some d -> is_mem _ (right_coset G H d) g.
  Proof.
    intros g d.
    unfold coset_repr.
    rewrite hd_error_cons.
    intros [l l_def].
    apply filter_inv in l_def.
    rewrite coset_swap; auto.
  Qed.

  Lemma canonical_right_coset_mem (G: finite_group) (H: subgroup G) g :
    canonical_right_coset G H g = g ->
    forall a, is_mem _ (right_coset G H g) a <-> canonical_right_coset G H a = g.
  Proof.
    intros CanonicalG a.
    unfold canonical_right_coset.
    remember (coset_repr G H a) as q.
    remember (coset_repr_always_some G H a).
    destruct q; [| contradict Heqq]; auto.
    symmetry in Heqq.
    rewrite coset_repr_mem, Heqq.
    - split; [intros Q; inversion Q | intros Q; rewrite Q]; auto.
    - unfold canonical_right_coset in CanonicalG.
      remember (coset_repr G H g) as q.
      remember (coset_repr_always_some G H g).
      destruct q; [| contradict Heqq]; auto.
      rewrite CanonicalG; reflexivity.
  Qed.

  Lemma canonical_right_coset_always_mem (G: finite_group) (H: subgroup G):
    forall g, is_mem _ (right_coset G H (canonical_right_coset G H g)) g.
  Proof.
    intros g.
    unfold canonical_right_coset.
    remember (coset_repr G H g) as q.
    destruct q.
    apply coset_repr_always_mem; auto.
    remember (coset_repr_always_some G H g) as Q.
    contradict HeqQ; auto.
  Qed.

  Lemma coset_reprs_unique (G: finite_group) (H: subgroup G):
    forall c d,
      coset_repr G H d = Some c ->
      coset_repr G H c = Some c.
  Proof.
    intros c d.
    unfold coset_repr.
    rewrite hd_error_cons.
    intros [l l_def].
    rewrite hd_error_cons.
    exists l.
    rewrite <- l_def.
    apply filter_eq.
    intros a.
    apply filter_inv in l_def.
    apply right_coset_mem_bool_rewrite.
    fold (is_mem G (right_coset G H d) c) in l_def.
    split; [ | rewrite coset_swap in l_def]; apply coset_trans; auto.
  Qed.

  (* proof is dumb *)
  Lemma canonical_right_coset_unique (G: finite_group) (H: subgroup G):
    forall c d,
      canonical_right_coset G H d = c ->
      canonical_right_coset G H c = c.
  Proof.
    intros c d.
    unfold canonical_right_coset.
    remember (coset_repr G H d) as q1.
    remember (coset_repr G H c) as q2.
    destruct q1; destruct q2; symmetry in Heqq1; symmetry in Heqq2.
    apply coset_reprs_unique in Heqq1.
    intros J; rewrite <- J, Heqq1 in Heqq2; inversion Heqq2; rewrite <- H1; auto.
    apply coset_reprs_unique in Heqq1; intros; reflexivity.
    remember (coset_repr_always_some G H d) as C; intros; contradict HeqC; auto.
    remember (coset_repr_always_some G H d) as C; intros; contradict HeqC; auto.
  Qed.

  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_I).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_X).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_Y).
  Compute (canonical_right_coset klein_group_finite klein_subgroup_X k_Z).

  Definition finite_coset (G: finite_group) (H: subgroup G) g :=
    (filter (right_coset G H g) (seq_g G)).

  Lemma finite_coset_NoDup (G: finite_group) (H: subgroup G) g :
    NoDup (finite_coset G H g).
  Proof.
    apply filter_NoDup, seq_listing.
  Qed.

  Lemma finite_coset_same_size_as_subgroup (G: finite_group) (H: finite_subgroup G):
    forall g, length (finite_coset G H g) = cardinality_subgroup G H.
  Proof.
    intros g.
    remember (fun c => c <*> (inv g)) as f.
    (* h \in H, take this to a coset of g *)
    apply (listisomorphism_NoDup_same_length _ _ f);
      [ | apply finite_coset_NoDup | apply subgroup_filter_NoDup; apply seq_listing].
    (* show this is an isomorphism *)
    split; try split.
    - rewrite Heqf.
      intros x y x_in y_in.
      apply (group_cancel_r _ (inv g)).
    - unfold ListSurjective.
      rewrite Heqf.
      intros c.
      unfold subgroup_filter.
      rewrite filter_In.
      intros [_ c_subgroup].
      exists (c <*> g).
      unfold finite_coset.
      rewrite filter_In.
      unfold right_coset.
      autorewrite with core.
      repeat split; try apply seq_listing; auto.
    - intros d.
      unfold finite_coset, subgroup_filter, right_coset.
      rewrite Heqf; repeat rewrite filter_In.
      repeat split; try apply seq_listing; tauto.
  Qed.
End finite_groups.

Section lagrange_theorem.

  Compute (let G := klein_group_finite in
          let H := klein_subgroup_X in
          let f := finite_coset G H in
          let f_inv := canonical_right_coset G H in
          (expand_partition G f_inv (seq_g G), partition_reprs G f_inv (seq_g G) (eq_dec G))).

  Definition unique_cosets (G: finite_group) (H: subgroup G) :=
    fold_right
      (set_add (eq_dec G))
      (empty_set G)
      (map (canonical_right_coset G H) (seq_g G)).

  Compute (unique_cosets klein_group_finite (klein_subgroup_X)).

    Check (let G := klein_group_finite in
          let H := klein_subgroup_X in
          let f := finite_coset G H in
          let f_inv := canonical_right_coset G H in
          expand_partition G f_inv (seq_g G)).

  Compute (let G := klein_group_finite in
          let H := klein_subgroup_X in
          let f := finite_coset G H in
          let f_inv := canonical_right_coset G H in
          expand_partition G f_inv (seq_g G)).

  Arguments op {g} _ _.
  Arguments inv {g} _.
  Notation "x <*> y" := (op x y) (at level 50, left associativity).

  Theorem cosets_are_partition (G: finite_group) (H: finite_subgroup G):
    fn_partition G
                 (canonical_right_coset G H)
                 (seq_g G)
                 (eq_dec G)
                 (cardinality_subgroup G H).
  Proof.
    apply fn_partition_intro.
    - apply seq_listing.
    - intros x.
      rewrite in_map_iff.
      intros [d [d_def _]].
      apply canonical_right_coset_unique in d_def.
      assumption.
    - intros a coset_equiv.
      rewrite <- (finite_coset_same_size_as_subgroup _ _ a).
      apply filter_length_equiv.
      intros b.
      destruct ((eq_dec G) (canonical_right_coset G H b) a);
        symmetry; [ | rewrite <- not_true_iff_false];
        fold (is_mem _ (right_coset G H a) b).
      apply canonical_right_coset_mem; auto.
      intros Not.
      apply canonical_right_coset_mem in Not; auto.
  Qed.

  Theorem lagrange_theorem : forall (G: finite_group) (H: finite_subgroup G),
      length (unique_cosets G H) * cardinality_subgroup G H =
      cardinality G.
  Proof.
    intros G H.
    unfold cardinality.
    remember (cosets_are_partition G H) as cosets_fn_partition.
    rewrite <- (expand_partition_same_size
                  _
                  (canonical_right_coset G H)
                  (seq_g G)
                  (eq_dec G)
                  (cardinality_subgroup G H)); auto.
    rewrite (expand_partition_length
                  _
                  (canonical_right_coset G H)
                  (seq_g G)
                  (eq_dec G)
                  (cardinality_subgroup G H)); auto.
  Qed.
End lagrange_theorem.

Section element_powers.
  Arguments z {g}.
  Arguments op {g} _ _.
  Arguments inv {g} _.
  Arguments eq_dec {g} _ _.

  Variable (G : Group).

  Notation "x ** y" := (op x y) (at level 50, left associativity).

  Fixpoint element_power (g: G) n : G :=
    match n with
    | 0 => z
    | S m => (g ** (element_power g m))
    end.

  Notation "g ^^ n" := (element_power g n) (at level 51, right associativity).

  Theorem element_power_0: forall g: G, g ^^ 0 = z.
  Proof.
    intros; simpl; autorewrite with core; auto.
  Qed.

  Theorem element_power_1: forall g: G, g ^^ 1 = g.
  Proof.
    intros; simpl; autorewrite with core; auto.
  Qed.

  Theorem element_power_z: forall n, z ^^ n = z.
  Proof.
    induction n; simpl; autorewrite with core; auto.
  Qed.

  Hint Rewrite element_power_0.
  Hint Rewrite element_power_1.
  Hint Rewrite element_power_z.

  Theorem element_power_additive: forall (g : G) m n,
      (g ^^ m) ** (g ^^ n) = g ^^ (m + n).
  Proof.
    intros g.
    induction m; intros; simpl; autorewrite with core; auto.
    rewrite IHm; auto.
  Qed.

  Theorem element_power_commutes: forall (g : G) m n,
      (g ^^ m) ** (g ^^ n) = (g ^^ n) ** (g ^^ m).
  Proof.
    intros; repeat rewrite element_power_additive; rewrite plus_comm; auto.
  Qed.

  Theorem element_power_single_commutes: forall (g : G) m,
      (g ^^m) ** g = g ** (g^^m).
  Proof.
    intros.
    rewrite <- (element_power_1 g) at 2.
    rewrite <- (element_power_1 g) at 3.
    rewrite element_power_commutes.
    autorewrite with core; auto.
  Qed.

  Lemma element_power_right  (g : G): forall n, (g ^^ n) ** g = g ^^ S n.
  Proof.
    induction n; simpl; autorewrite with core; auto.
    rewrite IHn; simpl; auto.
  Qed.

  Lemma element_power_left  (g : G): forall n, g ** (g ^^ n) = g ^^ S n.
  Proof.
    induction n; simpl; autorewrite with core; auto.
  Qed.

  Lemma element_power_inverse_right: forall (g: G) n m,
      n <= m -> (g ^^ m) ** ((inv g) ^^ n) = (g ^^ (m - n)).
  Proof.
    intros g.
    induction n.
    intros m; autorewrite with core; rewrite Nat.sub_0_r; auto.
    simpl.
    intros m H.
    rewrite <- element_power_single_commutes.
    rewrite op_assoc.
    rewrite IHn; try omega.
    apply (group_cancel_r _ g _ _).
    autorewrite with core.
    rewrite element_power_right.
    assert (S (m - S n) = m - n) as Rewrite by omega.
    rewrite Rewrite; auto.
  Qed.

  Lemma element_power_inverse_left: forall (g: G) n m,
      n <= m -> ((inv g) ^^ n) ** (g ^^ m) = (g ^^ (m - n)).
  Proof.
    intros g.
    induction n.
    intros m; autorewrite with core; rewrite Nat.sub_0_r; auto.
    simpl.
    intros m H.
    rewrite <- op_assoc.
    rewrite IHn; try omega.
    apply (group_cancel_l _ g _ _).
    autorewrite with core.
    rewrite element_power_left.
    assert (S (m - S n) = m - n) as Rewrite by omega.
    rewrite Rewrite; auto.
  Qed.

  Lemma element_power_inverse: forall (g: G) n,
      inv (g^^n) = (inv g)^^n.
  Proof.
    intros g; induction n; simpl; autorewrite with core; auto.
    rewrite IHn, element_power_right; auto.
  Qed.

  Hint Rewrite element_power_additive.
  Hint Rewrite element_power_inverse_right.
  Hint Rewrite element_power_inverse_left.
  Hint Rewrite element_power_inverse.
End element_powers.

Section element_order.
  Arguments z {g}.
  Arguments op {g} _ _.
  Arguments inv {g} _.
  Arguments eq_dec {g} _ _.

  Notation "x ** y" := (op x y) (at level 50, left associativity).
  Arguments element_power {G} _ _.
  Notation "g ^^ n" := (element_power g n) (at level 51, right associativity).

  Hint Rewrite element_power_additive.
  Hint Rewrite element_power_inverse_right.
  Hint Rewrite element_power_inverse_left.
  Hint Rewrite element_power_inverse.
  Hint Rewrite element_power_1.
  Hint Rewrite element_power_0.
  Hint Rewrite element_power_z.

  Definition iterated_powers (G: Group) (g : G) m : (list G) :=
    map (fun n => g ^^ n)  (List.seq 0 m).

  Lemma nth_error_seq : forall len start m,
      m < len -> nth_error (seq start len) m = Some (start + m).
  Proof.
    induction len.
    intros start m; omega.
    intros start m m_lt_Slen.
    simpl.
    destruct m.
    simpl; auto.
    simpl.
    apply lt_S_n, (IHlen (S start) m) in m_lt_Slen.
    rewrite m_lt_Slen, Nat.add_succ_comm; auto.
  Qed.

  Theorem iterated_powers_works (G: Group) : forall g n m h,
      nth_error (iterated_powers G g n) m = Some h -> g ^^ m = h.
  Proof.
    intros g n m h.
    unfold iterated_powers.
    intros H.
    cut (m < n).
    intros Cut.
    assert ((nth_error (map (fun n => g ^^ n) (seq 0 n)) m) = Some (g ^^ m)).
    apply map_nth_error, nth_error_seq; auto.
    rewrite H in H0.
    inversion H0; auto.
    assert (nth_error (map (fun n : nat => g ^^ n) (seq 0 n)) m <> None) as H'.
    contradict H.
    rewrite H; discriminate.
    apply nth_error_Some in H'.
    rewrite map_length, seq_length in H'.
    auto.
  Qed.

  Lemma iterated_powers_length (G: Group):
    forall g n, length (iterated_powers G g n) = n.
  Proof.
    intros g n; unfold iterated_powers; rewrite map_length, seq_length; auto.
  Qed.

  Theorem iterated_powers_works2 (G: Group): forall g n m,
      m < n -> nth_error (iterated_powers G g n) m = Some (g ^^ m).
  Proof.
    intros g n m m_lt_n.
    rewrite <- (iterated_powers_length G g) in m_lt_n.
    rewrite <- nth_error_Some in m_lt_n.
    remember (nth_error (iterated_powers G g n) m) as h.
    destruct h; [auto | contradict m_lt_n; auto].
    symmetry in Heqh; apply iterated_powers_works in Heqh; rewrite Heqh; auto.
  Qed.

  Lemma finite_group_iterated_powers_repeats (G: finite_group):
    forall g, ~ NoDup (iterated_powers G g (S (cardinality G))).
  Proof.
    intros g IteratedPowersNoDup.
    remember (S (cardinality G)) as N.
    assert (incl (iterated_powers G g N) (seq_g G)) as Powers_Subset.
    unfold incl; intros a H; apply seq_listing.
    apply (NoDup_incl_length IteratedPowersNoDup) in Powers_Subset.
    rewrite iterated_powers_length in Powers_Subset.
    rewrite HeqN in Powers_Subset.
    unfold cardinality in Powers_Subset.
    omega.
  Qed.

  Require Import Classical.

  (* must show this to be able to show power cycle
     approach requires classical logic - I imagine there is a way to do this
     with a more direct "find" *)
  Lemma not_nodup_means_different_elems: forall (A: Type) (l: list A),
      ~NoDup l ->
      (exists m i,
          m < length l
          /\ (m + i) < length l
          /\ i > 0
          /\ nth_error l m = nth_error l (m + i)).
  Proof.
    intros A.
    induction l; intros l_NoDup.
    contradict l_NoDup; apply NoDup_nil.
    rewrite NoDup_cons_iff in l_NoDup.
    apply not_and_or in l_NoDup.
    destruct l_NoDup as [In_a | Not_NoDup].
    apply NNPP in In_a.
    apply in_split in In_a.
    destruct In_a as [l1 [l2 l_eq]].
    exists 0; exists (S (length l1)).
    repeat split; try simpl; try omega; rewrite l_eq.
    rewrite app_length; simpl; try omega.
    rewrite nth_error_app2; try omega.
    rewrite Nat.sub_diag; simpl; auto.
    (* induction step, must 'step forward' and add 1 to both m and n *)
    apply IHl in Not_NoDup.
    destruct Not_NoDup as [m [n [m_length [n_bounded [n_gt_0 list_eq]]]]].
    exists (S m); exists n.
    repeat split; try simpl; try omega; auto.
  Qed.

  Lemma power_cycle (G: Group) (g: G): forall m n,
      n > m -> g ^^n = g^^m -> g ^^ (n - m) = z.
  Proof.
    induction m; intros n; autorewrite with core.
    rewrite Nat.sub_0_r; auto.
    Search (_ - S _).
    intros n_gt_Sm.
    simpl.
    intros H.
    (* would be nice to not do everything in H here *)
    apply (group_add_r _ ((inv g)^^m)) in H.
    rewrite <- op_assoc in H.
    rewrite element_power_inverse_right in H; try omega.
    rewrite element_power_inverse_right in H; try omega.
    rewrite Nat.sub_diag in H.
    simpl in H.
    autorewrite with core in H.
    apply (group_cancel_r _ g).
    rewrite element_power_right.
    replace (S (n - S m)) with (n -  m); try omega.
    autorewrite with core; auto.
  Qed.

  Theorem every_finite_group_element_has_a_power_cycle (G: finite_group):
    forall (g : G), exists m, 0 < m < S (cardinality G) /\ g^^m = z.
  Proof.
    intros g.
    remember (finite_group_iterated_powers_repeats G g) as RepeatedCycles.
    destruct HeqRepeatedCycles.
    remember (S (cardinality G)) as N.
    apply not_nodup_means_different_elems in RepeatedCycles.
    destruct RepeatedCycles as [m [i [m_lt_len [n_lt_len [i_gt_0 Cycle]]]]].
    assert ((nth_error (iterated_powers G g N) m) = Some (g ^^ m)) as G_power_m.
    apply iterated_powers_works2;
      rewrite iterated_powers_length in m_lt_len; auto.
    assert ((nth_error (iterated_powers G g N) (m + i)) = Some (g ^^ (m + i))) as G_power_n.
    apply iterated_powers_works2;
      rewrite iterated_powers_length in n_lt_len; auto.
    rewrite iterated_powers_length in n_lt_len.
    rewrite iterated_powers_length in m_lt_len.
    rewrite G_power_m, G_power_n in Cycle.
    exists i.
    repeat split; try omega.
    inversion Cycle as [A].
    symmetry in A; apply power_cycle in A; replace (m + i - m) with i in A; try omega; auto.
  Qed.

  Lemma power_cycle_mult (G: Group):
    forall (g: G) (k m: nat), g ^^m = z -> g ^^ k * m = z.
  Proof.
    intros g; induction k; intros m g_cycle; simpl; auto.
    rewrite <- element_power_additive.
    rewrite g_cycle.
    autorewrite with core.
    apply IHk; auto.
  Qed.

  Lemma power_cycle_mod (G: Group):
    forall (g: G) (m n: nat), m > 0 -> (g ^^ m = z) -> (g ^^ n) = g ^^ (n mod m).
  Proof.
    intros g m n m_gt_0 m_power.
    assert (g ^^ (m * (n / m)) = z).
    rewrite Nat.mul_comm; apply power_cycle_mult; auto.
    apply (group_cancel_r _ z).
    rewrite <- H0 at 2.
    autorewrite with core.
    rewrite plus_comm.
    rewrite <- (Nat.div_mod n m); auto; try omega.
  Qed.

  Lemma iterated_powers_contains_z (G: Group):
    forall (g: G) n, n > 0 -> In z (iterated_powers G g n).
  Proof.
    intros g.
    induction n; intros n_gt_0; try omega.
    simpl; left; auto.
  Qed.

  (* what I really want to show is that the first m powers are unique
     (no duplicates).  where this is challenging is that the k we get from the
     power cycle lemma above is not guaranteed to be the first k *)

  Lemma combine_nil :forall (C D: Type) (l': list C), combine l' (@nil D) = [].
  Proof.
    induction l'; auto.
  Qed.

  Lemma combine_nil2 :forall (C D: Type) (l': list C), combine (@nil D) l' = [].
  Proof.
    induction l'; auto.
  Qed.

  Lemma combine_seq: forall (C: Type) l m (b : C) len,
      len > 0 ->
      combine (seq m len) (b :: l) = (m, b) :: (combine (seq (m + 1) (len - 1)) l).
  Proof.
    intros C; induction l; intros m b len; simpl.
    rewrite combine_nil; simpl.
    destruct len;
      [intros; omega |
       simpl; rewrite combine_nil; intros; reflexivity].
    intros len_gt_0.
    destruct len.
    contradict len_gt_0; omega.
    simpl.
    replace (len - 0) with len by omega.
    replace (S m) with (m + 1) by omega.
    reflexivity.
  Qed.

  (* ugly proof *)
  Theorem combine_nth_error (A B: Type): forall n (l1: list A) (l2: list B) h j,
      (nth_error l1 n = Some h /\ nth_error l2 n = Some j) <->
      nth_error (combine l1 l2) n = Some (h, j).
  Proof.
    induction n; simpl; intros l1 l2 h j; split.
    intros [nth_l1 nth_l2]; destruct l1; destruct l2; simpl; try discriminate.
    inversion nth_l1; inversion nth_l2; auto.
    intros l1_l2_combine; destruct l1; destruct l2;
      try rewrite combine_nil in l1_l2_combine;
      try rewrite combine_nil2 in l1_l2_combine;
      [ | | | simpl in l1_l2_combine; inversion l1_l2_combine; tauto];
      contradict l1_l2_combine; discriminate.
    intros [nth_l1 nth_l2]; destruct l1; destruct l2; simpl; try discriminate.
    apply IHn; tauto.
    intros l1_l2_combine.
    destruct l1; destruct l2;
      try rewrite combine_nil in l1_l2_combine;
      try rewrite combine_nil2 in l1_l2_combine;
      [ | | | simpl in l1_l2_combine; inversion l1_l2_combine; apply IHn ; tauto];
      contradict l1_l2_combine; discriminate.
  Qed.

  Theorem combine_nth_error2 (A B: Type): forall (l1: list A) (l2: list B) h j,
      In (h, j) (combine l1 l2) -> exists n, nth_error l1 n = Some h /\ nth_error l2 n = Some j.
  Proof.
  Admitted.

  Definition powers_of_g (G: finite_group) (g: G) :=
    let n := S (cardinality G) in
    combine (seq 0 n) (iterated_powers G g n).

  Theorem nth_error_Some2 : forall (A: Type) (l : list A) (n : nat) b,
      nth_error l n = Some b -> n < length l.
  Proof.
    intros A l n b.
    remember (nth_error_Some l n) as OtherLemma.
    intros H.
    apply OtherLemma; rewrite H; discriminate.
  Qed.

  Theorem in_powers_of_g (G: finite_group) (g: G) : forall m h,
      In (m, h) (powers_of_g G g) <-> 0 <= m < (S (cardinality G)) /\ g^^m = h.
  Proof.
    intros m h.
    unfold powers_of_g.
    remember (S (cardinality G)) as N.
    split.
    - intro H_in_zip.
      assert (0 <= m < N) as m_bound.
      apply in_combine_l, in_seq in H_in_zip; omega.
      destruct (combine_nth_error2 _ _ _ _ m h H_in_zip) as [n [nth_eq nth_power]].
      assert (n < N) as n_bound.
      apply nth_error_Some2 in nth_eq; rewrite seq_length in nth_eq; auto.
      remember (nth_error_seq N 0 n).
      replace m with (0 + m) in nth_eq by omega; apply (nth_error_seq N 0 _) in n_bound.
      rewrite n_bound in nth_eq.
      inversion nth_eq as [m_eq_n].
      rewrite m_eq_n in nth_power.
      split; [omega | apply (iterated_powers_works _ _ N _ _)]; auto.
    - intros [m_bound m_eq].
      assert (m < N) as m_lt_bound by omega.
      assert (m < N) as m_lt_bound2 by omega.
      apply (nth_error_seq _ 0 _) in m_lt_bound.
      simpl in m_lt_bound.
      apply (iterated_powers_works2 G g) in m_lt_bound2.
      apply (nth_error_In _ m), combine_nth_error; rewrite <- m_eq; split; assumption.
  Qed.

  Definition nonzero_powers (G: finite_group) (g: G) := tail (powers_of_g G g).
  Definition is_pair_zero (G: finite_group) :=
    (fun (p: (nat * G)) => if eq_dec (snd p) z then true else false).

  Definition order (G: finite_group) (g : G) :=
    fst (hd (0, z) (filter (is_pair_zero G) (nonzero_powers G g))).

  Lemma order_filter_nonempty (G: finite_group) (g : G):
    exists p tl, (filter (is_pair_zero G) (nonzero_powers G g)) = p :: tl.
  Proof.
    destruct (every_finite_group_element_has_a_power_cycle G g) as
        [h [h_bound g_to_h]].
    assert (In (h, z) (powers_of_g G g)) as in_powers_of_g.
    apply in_powers_of_g; split; try omega; auto.
    assert (In (h, z) (nonzero_powers G g)) as in_nonzero_powers.
    unfold powers_of_g, iterated_powers; unfold nonzero_powers; simpl.
    apply (nth_error_In _ (h - 1)), combine_nth_error.
    split; [ | rewrite <- g_to_h; apply map_nth_error]; replace h with (1 + (h - 1)) at 2 by omega; apply nth_error_seq; omega.
    assert (In (h, z) (filter (is_pair_zero G) (nonzero_powers G g))) as in_filter.
    apply filter_In; try split; auto; simpl; unfold is_pair_zero; simpl; destruct (@eq_dec G z z); auto.
    assert (filter (is_pair_zero G) (nonzero_powers G g) <> []) as NonZeroFilter.
    remember (filter (is_pair_zero G) (nonzero_powers G g)) as Q; destruct Q;
      [contradict in_filter | discriminate].
    remember (filter (is_pair_zero G) (nonzero_powers G g)) as Q; destruct Q;
      [contradict NonZeroFilter | auto]; auto.
    exists p; exists Q; auto.
  Qed.

  Lemma order_filter_cut (G: finite_group) (g: G): forall a b,
      In (a, b) (filter (is_pair_zero G) (nonzero_powers G g)) -> a > 0.
  Proof.
    intros a b.
    Search (In _ (filter _ _)).
    rewrite filter_In.
    unfold nonzero_powers, powers_of_g.
    simpl.
    Search (In _ (combine _ _)).
    intros [H _].
    apply in_combine_l in H.
    rewrite in_seq in H; omega.
  Qed.

  Theorem order_always_positive (G: finite_group) (g : G):
    order G g > 0.
  Proof.
    unfold order.
    destruct (order_filter_nonempty G g) as [x [tl x_eq]].
    rewrite x_eq.
    simpl.
    destruct x.
    assert (In (n, a) (filter (is_pair_zero G) (nonzero_powers G g))).
    (* dumb, but works *)
    destruct (nonzero_powers G g);
      [simpl in x_eq; contradict x_eq; discriminate | rewrite x_eq; simpl; tauto].
    apply (order_filter_cut _ g n a); assumption.
  Qed.

  Lemma nth_error_empty: forall (A: Type) n, @nth_error A [] n = None.
  Proof.
    intros A; induction n; simpl; reflexivity.
  Qed.

  Lemma nth_error_empty2: forall (A: Type) n a, @nth_error A [] n <> Some a.
  Proof.
    intros A; induction n; simpl; discriminate.
  Qed.

  Lemma nth_error_map2: forall (A B: Type) (l: list A) (f: A -> B) (n: nat) (b: B),
      nth_error (map f l) n = Some b -> exists a, nth_error l n = Some a /\ f a = b.
  Proof.
    intros A B; induction l; intros f n b nth_error_eq.
    simpl in nth_error_eq.
    remember (nth_error_empty2 B n b) as Q.
    contradict nth_error_eq; assumption.
    destruct n; simpl in nth_error_eq.
    inversion nth_error_eq.
    exists a; simpl; tauto.
    apply IHl in nth_error_eq.
    destruct nth_error_eq as [c H].
    exists c.
    simpl; tauto.
  Qed.

  Theorem element_raised_to_order (G: finite_group) (g: G):
    g ^^ (order G g) = z.
  Proof.
    unfold order.
    unfold powers_of_g.
    destruct (order_filter_nonempty G g) as [p [l H]].
    rewrite H; simpl.
    unfold nonzero_powers in H.
    destruct p as [m h].
    (* feels like we need this, but maybe we don't *)
    assert (In (m, h) (filter (is_pair_zero G) (tl (powers_of_g G g)))) as H1.
    rewrite H; simpl; left; tauto.
    assert (h = z) as H2.
    apply filter_In in H1; destruct H1 as [_ PairZero].
    unfold is_pair_zero in PairZero.
    simpl in PairZero; destruct (eq_dec h z);
      [assumption | contradict PairZero; discriminate].
    Search (In _ (filter _ _)).
    apply filter_In in H1.
    destruct H1 as [H1 _].
    unfold powers_of_g in H1.
    (* must show g ^^ m = h *)
    unfold iterated_powers in H1; simpl in H1.
    apply combine_nth_error2 in H1.
    destruct H1 as [i [i_value i_power]].
    remember (nth_error_Some2 _ _ _ _ i_value) as i_bound.
    destruct Heqi_bound.
    rewrite seq_length in i_bound.
    rewrite (nth_error_seq (cardinality G) _ i i_bound) in i_value.
    inversion i_value as [m_eq_Si].
    (* must finally show result through i_power *)
    Search (nth_error (seq _ _) _).
    apply nth_error_map2 in i_power.
    destruct i_power as [a [a_value a_equal]].
    rewrite nth_error_seq, i_value in a_value by omega.
    inversion a_value as [m_eq_a]. rewrite m_eq_Si, m_eq_a.
    simpl; rewrite <- H2; assumption.
  Qed.

  Compute (order klein_group_finite k_Y).

  Arguments order {G0} _.

  Lemma order_bound (G: finite_group) (g: G) :
    order g <= (cardinality G).
  Proof.
    unfold order.
    unfold nonzero_powers.
    remember (filter (is_pair_zero G) (tl (powers_of_g G g))) as q.
    destruct q; simpl.
    - omega.
    - cut (In p (tl (powers_of_g G g))).
      intros Cut.
      simpl in Cut.
      destruct p.
      simpl.
      apply in_combine_l, in_seq in Cut; omega.
      cut (In p (filter (is_pair_zero G) (tl (powers_of_g G g)))).
      rewrite filter_In; tauto.
      rewrite <- Heqq; simpl; tauto.
  Qed.

  Definition smallest_power_cycle (G: Group) (g : G) (n : nat) :=
    n > 0 /\ g^^n = z /\ (forall m, 0 < m < n -> g^^m <> z).

  Lemma filter_split: forall (A: Type) (l l': list A) f b,
      filter f l = b :: l' -> exists l2 l3, l = l2 ++ b :: l3 /\ forall b, In b l2 -> f b = false.
  Proof.
    induction l; intros l' f b; simpl; intro filter_eq.
    contradict filter_eq; discriminate.
    destruct (bool_dec (f a) true) as [fa_true | fa_false].
    rewrite fa_true in filter_eq.
    inversion filter_eq as [a_eq_b].
    exists []; exists l; simpl; split; [reflexivity | intros b' H'; contradict H'].
    Search (_ <> true).
    apply not_true_is_false in fa_false.
    rewrite fa_false in filter_eq.
    apply IHl in filter_eq.
    destruct filter_eq as [l2 [l3 [l_eq l_not_contains]]].
    exists (a :: l2), l3.
    split; [rewrite l_eq; reflexivity | simpl; intros c].
    intros [a_eq_c | c_in_l2]; [rewrite <- a_eq_c | apply l_not_contains]; assumption.
  Qed.

  Lemma filter_combine: forall (A: Type) (l: list A) f m len,
      forall j q, In (j, q) (filter f (combine (seq m len) l)) -> m <= j.
  Proof.
    intros A; induction l; intros f m len j q in_jq.
    rewrite combine_nil in in_jq; contradict in_jq.
    assert (len > 0) as len_gt_0.
    destruct len;
      [simpl in in_jq; contradict in_jq; discriminate | omega].
    rewrite combine_seq in in_jq; auto.
    simpl in in_jq.
    destruct (bool_dec (f (m, a)) true) as [fma | fma];
      [ | apply not_true_is_false in fma]; rewrite fma in in_jq.
    simpl in in_jq.
    destruct in_jq as [ma_first | in_rest];
      [inversion ma_first | apply (IHl f (m + 1)) in in_rest]; omega.
    apply IHl in in_jq; omega.
  Qed.

  Lemma empty_list_not_equal_app (A: Type):
    forall (l1 l2: list A) (a: A), [] <> l1 ++ a :: l2.
  Proof.
    induction l1; simpl.
    discriminate.
    intros H; inversion H; intros a0; discriminate.
  Qed.

  Lemma combine_seq2 (B: Type): forall (l: list B) start len p l2,
      combine (seq start len) l = p :: l2 ->
      fst p = start /\
      combine (seq (start + 1) (len - 1)) (tl l) = l2.
  Proof.
    induction l; intros start len p l2.
    rewrite combine_nil; intros CombineEq; contradict CombineEq; discriminate.
    intros CombineEq.
    assert (~(len = 0)) as LengthNotZero.
    intros Not; rewrite Not in CombineEq;
      simpl in CombineEq; contradict CombineEq; discriminate.
    rewrite combine_seq in CombineEq; [| omega].
    inversion CombineEq as [[hd l']]; simpl; tauto.
  Qed.

  Lemma seq_step: forall start len,
      len > 0 ->
      seq start len = start :: seq (start + 1) (len - 1).
  Proof.
    intros start; destruct len.
    intros H; contradict H; omega.
    intros H; simpl; replace (start + 1) with (S start) by ring; rewrite Nat.sub_0_r; reflexivity.
  Qed.

  Lemma combine_seq_map_l (B: Type): forall (l: list B) start len,
      length l = len ->
      seq start len = map fst (combine (seq start len) l).
  Proof.
    induction l; intros start len; simpl.
    rewrite combine_nil; intros H; symmetry in H; rewrite H; simpl; reflexivity.
    intros H.
    rewrite combine_seq; simpl; [|omega].
    rewrite <- (IHl (start + 1) (len - 1)), <- seq_step; [reflexivity|omega|omega].
  Qed.

  Lemma combine_seq_bound (A: Type):
    forall l' (l: list A) p start len,
      combine (seq start len) l = p :: l' ->
      (forall p', In p' l' -> fst p < fst p').
  Proof.
    induction len.
    simpl.
    intros H; contradict H; discriminate.
    intros CombineEq.
    simpl in CombineEq.
    destruct l.
    * contradict CombineEq; discriminate.
    * inversion CombineEq as [[start_eq_p combine_eq]].
      intros p' In_p'; destruct p' as [n b].
      apply in_combine_l, in_seq in In_p'; simpl; omega.
  Qed.

  (*
  Lemma combine_seq_tail (A: Type):
    forall (l: list A) start len,
      len > 0 ->
      length l >= len ->
      exists l' b,
        combine (seq start len) l = combine (seq start (len - 1)) l' ++ [(start + len, b)].
  Proof.
    induction l; intros start len LenGt0 LengthBound.
    contradict LengthBound; simpl; omega.
    destruct l.
    exists [].
    exists a.
    rewrite combine_nil.

    simpl.
    Check (IHl start len LenGt0).

  Admitted.

  Lemma combine_app_split (A: Type):
    forall n (l: list A) start len,
      n < len ->
      length l >= len ->
      exists (l1 l2: list A),
        combine (seq start len) l =
        combine (seq start n) l1 ++
                combine (seq (start + n) (len - n)) l2.
  Proof.
    induction n; intros l start len n_bound length_bound; simpl.
    exists []; exists l; rewrite Nat.add_0_r, Nat.sub_0_r; reflexivity.
    assert (n  < len) as NBound by omega.
    remember (IHn l start len NBound length_bound) as Q.
    destruct Q as [l1' [l2' l_eq]]; destruct HeqQ.

    case n.
    simpl.

    exists []

    destruct l.
    exists []; exists []; repeat rewrite combine_nil; autorewrite with list; reflexivity.
    rewrite l_eq.
    exists (a :: l).
    replace (S start) with (start + 1) by ring.
    replace n with (n + 1 - 1).
    rewrite <- combine_seq.
    replace (n + 1 - 1) with n.

    destruct l1'.
    rewrite combine_nil in l_eq.



    (*

      exists [].
      exists l2'.
      simpl.

          rewrite l_eq.




    simpl.
    induction l; intros start len n NBound LengthBound.
    rewrite combine_nil.
    exists []; exists []; repeat rewrite combine_nil; simpl; reflexivity.
    rewrite combine_seq; [|omega].
    remember (len - 1) as LengthMinus 1.
    destruct (len - 1); destruct n; simpl.
    - exists []; exists [a]; rewrite combine_seq;
        [simpl; rewrite combine_nil, Nat.add_0_r; reflexivity|omega].
    - exists [a]; exists []; repeat rewrite combine_nil; rewrite app_nil_r; reflexivity.
    - exists [].
      destruct l.
      exists [a].
      rewrite combine_seq, combine_nil, Nat.add_0_r; [reflexivity | omega].
      remember (IHl (S (start + 1)) n0).
      exists [a; a0].
      simpl.


      rewrite combine_nil.

      ; exists [a]; rewrite combine_seq; try omega; rewrite combine_nil.



    simpl.
    exists [a]; exists []; rewrite combine_nil.


    cut (n - 1 < len - 1).
    intros Cut.
    cut (length l >= len - 1).
    intros Cut2.
    remember (IHl (start + 1) (len - 1) (n - 1) Cut Cut2) as Q.


    destruct Q as [l1' l2'].
    re

  .
     *)


  Lemma combine_split_bound (A: Type):
    forall l2 (l: list A) p l3 start len,
      combine (seq start len) l = l2 ++ p :: l3 ->
      (forall p', In p' l2 -> fst p' < fst p) /\
      (forall p', In p' l3 -> fst p < fst p').
  Proof.
    induction l2; intros l p l3 start len; simpl; intros combine_eq; split; intros [n b].
    - tauto.
    - intros In_l3.
      apply combine_seq2 in combine_eq.
      destruct combine_eq as [fst_p combine_eq]; rewrite fst_p.
      rewrite <- combine_eq in In_l3.
      apply in_combine_l,  in_seq in In_l3.
      simpl; omega.
    - intros [a_eq | In_l2].
      * (* a = (n, b) -- *)

        apply combine_seq2 in combine_eq.
      destruct combine_eq as [H1 H2].
      apply IHl2 in H2.
      destruct H2 as [lower_bound upper_bound].
      rewrite <- a_eq, H1.
      (* lost ability to say anything about l2 / l3 *)


    -

    - intros H.
      split; intros [n a]; [intros H'; contradict H' | auto].
      apply combine_seq2 in H.
      destruct H as [fst_p combine_eq]; rewrite fst_p.
      simpl; omega.
    -
      split.






  Admitted.
 *)

  Lemma combine_seq_length (A: Type):
    forall l2 (l: list A)  start len (p: nat * A) l3,
      combine (seq start len) l = l2 ++ p :: l3 -> length l2 = fst p - start.
  Proof.
    induction l2; intros l start len p l3; simpl.
    - intros H; apply combine_seq2 in H; destruct H as [start_eq _];
        rewrite start_eq; auto with arith.
    - intros H.
      assert (combine (seq start len) l = a :: l2 ++ p :: l3) as H' by assumption.

      (*remember (combine_seq_bound A (l2 ++ p :: l3) l a start len H p).*)


      (*apply (combine_split_bound A l (a :: l2) p l3 start len) in H.*)
      cut (fst a < fst p).
      intros Cut.
      apply combine_seq2 in H'; destruct H' as [start_eq combine_rest].
      apply IHl2 in combine_rest; rewrite combine_rest.
      omega.
      apply (combine_seq_bound A (l2 ++ p :: l3) l a start len H p).
      Search (In _).
      rewrite in_app_iff; right; simpl; left; reflexivity.
  Qed.

  (* show order is smallest power cycle *)
  Theorem order_is_smallest  (G: finite_group) (g : G) :
    (smallest_power_cycle G g) (order g).
  Proof.
    unfold smallest_power_cycle.
    remember (order_bound G g) as OrderBound.
    destruct HeqOrderBound.
    repeat split;
      [apply order_always_positive | apply element_raised_to_order | auto].
    intros m m_lt_g Not.
    (* the approach here should be that order g was the first *)
    remember (order g) as n.
    assert (n = order g) as n_is_order_g by assumption.
    unfold order in n_is_order_g.
    destruct (order_filter_nonempty G g) as [p [l p_rest]].
    rewrite p_rest in n_is_order_g; simpl in n_is_order_g.
    apply filter_split in p_rest.
    destruct p_rest as [l2 [l3 [l2_l3_eq no_z_smaller]]].
    assert (In (m, z) (powers_of_g G g)) as InMz.
    apply in_powers_of_g; split; [omega | auto].
    assert (In (m, z) l2) as Contradiction.
    unfold nonzero_powers in l2_l3_eq.
    simpl in l2_l3_eq.
    apply (nth_error_In l2 (m - 1)).
    rewrite <- (nth_error_app1 _ (p :: l3)), <- l2_l3_eq, <- combine_nth_error.
    replace m with (1 + (m - 1)) at 2 by omega.
    split; [ |
            rewrite <- Not; apply map_nth_error;
            replace m with (1 + (m - 1)) at 2 by omega]; apply nth_error_seq; omega.
    (* show m - 1 < length l2, which it should be *)
    apply combine_seq_length in l2_l3_eq; auto; omega.
    (* once we have the bound on m it is straightforward *)
    apply no_z_smaller in Contradiction.
    unfold is_pair_zero in Contradiction.
    simpl in Contradiction; destruct (eq_dec z z) as [always | impossible];
      contradict Contradiction.
    discriminate.
    contradict impossible; reflexivity.
  Qed.

  Lemma powers_of_g_nth_error (G: finite_group) (g: G) :
    forall n m a, nth_error (powers_of_g G g) n = Some (m, a) -> m = n /\ g ^^ m = a.
  Proof.
    intros n m a Hma.
    assert (n < S (cardinality G)) as n_bound.
    apply nth_error_Some2 in Hma; unfold powers_of_g in Hma;
      rewrite combine_length, seq_length, iterated_powers_length in Hma;
      rewrite Nat.min_id in Hma; assumption.
    assert (In (m, a) (powers_of_g G g)) as ma_in_powers.
    apply nth_error_In in Hma; assumption.
    rewrite in_powers_of_g in ma_in_powers.
    unfold powers_of_g in Hma.
    rewrite <- combine_nth_error in Hma.
    destruct Hma as [Hm Hn].
    apply iterated_powers_works in Hn.
    rewrite nth_error_seq in Hm; [ simpl in Hm; inversion Hm; tauto | assumption ].
  Qed.


  (* show the element powers are a subgroup *)

  Definition element_subgroup_mem (G: finite_group) (g : G) : (set G) :=
    let power_list := iterated_powers G g (S (cardinality G)) in
    (fun h => match count_occ eq_dec power_list h with
                                      0 => false
                                    | _ => true
                                    end).

  Lemma iterated_powers_in (G : Group) (g: G): forall a n,
      In a (iterated_powers G g n) <-> exists m, m < n /\ g ^^ m = a.
  Proof.
    intros a n; unfold iterated_powers; rewrite in_map_iff.
    split; simpl.
    intros [x [g_to_x x_in_seq]].
    exists x.
    apply in_seq in x_in_seq; split; auto; omega.
    intros [m [m_lt_n g_to_m]].
    exists m.
    split; auto; apply in_seq; omega.
  Qed.

  Lemma element_subgroup_mem_exists_n (G: finite_group) (g : G) :
    forall a,
      is_mem G (element_subgroup_mem G g) a <->
      (exists n,
          n < S (cardinality G) /\
          g ^^ n = a).
  Proof.
    intros a.
    unfold element_subgroup_mem, is_mem.
    remember (count_occ eq_dec _ a) as Q.
    split.
    destruct Q; intros H.
    contradict H; auto.
    assert (count_occ eq_dec
                      (iterated_powers G g (S (cardinality G))) a > 0) as H1
      by omega.
    apply count_occ_In in H1.
    apply (iterated_powers_in _ _ _ (S (cardinality G))); auto.
    intros [n [n_bounded g_to_n]].
    apply (iterated_powers_works2 G g (S (cardinality G))) in n_bounded.
    apply nth_error_In in n_bounded.
    rewrite g_to_n in n_bounded.
    apply (count_occ_In eq_dec) in n_bounded.
    destruct Q; try omega; auto.
  Qed.

  Lemma element_subgroup_mem_z (G: finite_group) (g: G) :
    is_mem G (element_subgroup_mem G g) z.
  Proof.
    assert (S (cardinality G) > 0) as Gt by omega.
    remember (iterated_powers_contains_z G g (S (cardinality G)) Gt) as Q.
    destruct HeqQ.
    unfold is_mem, element_subgroup_mem.
    rewrite (count_occ_In eq_dec _ _) in Q.
    destruct (count_occ eq_dec _ z); try omega; auto.
  Qed.

  Lemma element_subgroup_mem_closed (G: finite_group) (g : G) :
    forall a b,
      is_mem G (element_subgroup_mem G g) a /\
      is_mem G (element_subgroup_mem G g) b ->
      is_mem G (element_subgroup_mem G g) (a ** b).
  Proof.
    intros a b [a_mem b_mem].
    remember (order_always_positive G g) as order_positive.
    remember (order_bound G g) as order_bounded.
    apply element_subgroup_mem_exists_n in a_mem.
    apply element_subgroup_mem_exists_n in b_mem.
    destruct a_mem as [h [h_bound g_to_h]].
    destruct b_mem as [i [g_bound g_to_i]].
    rewrite <- g_to_h, <- g_to_i.
    rewrite element_power_additive.
    (* h + i % group order *)
    assert (g ^^ (h + i) = g ^^ ((h + i) mod (order g))) as ThingWeCanProve.
    apply power_cycle_mod; [apply order_always_positive | apply element_raised_to_order].
    rewrite ThingWeCanProve.
    assert (((h + i) mod (order g)) < (order g)).
    apply Nat.mod_upper_bound; omega.
    assert (((h + i) mod (order g)) < (S (cardinality G))) by omega.
    apply element_subgroup_mem_exists_n.
    exists ((h + i) mod (order g)); auto.
  Qed.

  Lemma element_subgroup_mem_inverse (G: finite_group) (g : G) :
    forall a,
      is_mem G (element_subgroup_mem G g) a ->
      is_mem G (element_subgroup_mem G g) (inv a).
  Proof.
    intros a a_mem.
    apply element_subgroup_mem_exists_n in a_mem.
    destruct a_mem as [h [h_bound g_to_h]].
    remember (order_always_positive G g) as order_positive.
    remember (order_bound G g) as order_bounded.
    apply element_subgroup_mem_exists_n.
    destruct (lt_eq_lt_dec h (order g)) as [[h_lt_k | h_eq_k] | h_gt_k].
    exists ((order g) - h).
    split; try omega.
    rewrite <- g_to_h.
    rewrite element_power_inverse.
    apply (group_cancel_r _ (g ^^ h)).
    autorewrite with core; try omega.
    replace ((order g) - h + h) with (order g) by omega.
    rewrite Nat.sub_diag.
    autorewrite with core; apply element_raised_to_order.
    (* option 2, h = k *)
    exists (order g).
    rewrite h_eq_k, element_raised_to_order in g_to_h.
    rewrite <- g_to_h; rewrite element_raised_to_order; split;
      [omega | autorewrite with core; reflexivity].
    (* option 3, h > k *)
    (* cycle is at k = 5, we are given h = 12 *)
    (* actual inverse is at 3 *)
    (* we first replace with the case *)
    exists ((order g) - (h mod (order g))).
    split; try omega.
    assert (g ^^ h = g ^^ h mod (order g)) as replace_mod.
    apply power_cycle_mod; [omega | apply element_raised_to_order].
    rewrite replace_mod in g_to_h.
    rewrite <- g_to_h.
    apply (group_cancel_r _ (g ^^ (h mod (order g)))).
    autorewrite with core; auto.
    assert (h mod (order g) < (order g)) as h_mod_k_bound.
    apply Nat.mod_upper_bound; omega.
    replace ((order g) - h mod (order g) + h mod (order g)) with (order g) by omega.
    rewrite Nat.sub_diag.
    autorewrite with core; apply element_raised_to_order; reflexivity.
  Qed.

  Definition element_subgroup (G: finite_group):
    forall (g: G), subgroup G.
  Proof.
    intros g.
    remember (iterated_powers G g (S (cardinality G))) as power_list.
    apply (makeSubgroup G (element_subgroup_mem G g)).
    apply (element_subgroup_mem_z G g).
    apply (element_subgroup_mem_closed G g).
    apply (element_subgroup_mem_inverse G g).
  Defined.

  Definition element_subgroup_finite (G: finite_group):
    forall (g: G), finite_subgroup G.
  Proof.
    intros g.
    apply (makeFiniteSubgroup G (element_subgroup G g)
                              (fold_right (set_add eq_dec) (empty_set G)
                                          (iterated_powers G g (S (cardinality G))))).
    intros h.
    rewrite fold_set_add_in, (element_subgroup_mem_exists_n G g h), iterated_powers_in; tauto.
    apply fold_set_NoDup; reflexivity.
  Defined.

  Lemma mod_squeeze: forall a b c, c <> 0 -> a >= b -> a < c -> b < c -> (a - b) mod c = 0 <-> a = b.
  Proof.
    intros a b c c_eq_0 a_lt_c b_lt_c.
    split; [ | intros H; rewrite H; rewrite Nat.sub_diag, Nat.mod_0_l; auto].
    intros ModSqueeze.
    destruct (lt_eq_lt_dec a b) as [[a_lt_b | a_eq_b] | a_gt_b]; try omega.
    rewrite Nat.mod_divide in ModSqueeze; [|assumption]; try omega; apply Nat.divide_pos_le in ModSqueeze; omega.
  Qed.

  Theorem power_isomorphism (G: finite_group) (g: G):
    ListIsomorphism (fun n => g^^n)
                    (seq 0 (order g))
                    (filter (fun a : G => element_subgroup_mem G g a) (seq_g G)).
  Proof.
    remember (order_always_positive G g) as OrderPositive.
    remember (order_bound G g) as OrderBound.
    assert (order g <> 0) as OrderNeq0 by omega.
    repeat split.
    - (* injectivity: must use order g is minimum here *)
      remember (order_is_smallest G g) as SmallestPowerCycle.
      unfold smallest_power_cycle in SmallestPowerCycle.
      destruct SmallestPowerCycle as [OrderGt0 [OrderPowerCycle BoundRaiseToZ]].
      intros m n m_bound n_bound gm_eq_gn.
      rewrite in_seq in m_bound.
      rewrite in_seq in n_bound.
      destruct (lt_eq_lt_dec m n) as [[m_lt_n | m_eq_n] | m_gt_n];
        [ remember ((n - m) mod (order g)) as Value; symmetry in gm_eq_gn |
          assumption |
          remember ((m - n) mod (order g)) as Value];
        apply power_cycle in gm_eq_gn; [|omega | |omega];
          rewrite (power_cycle_mod _ _ (order g)) in gm_eq_gn; try assumption;
          assert (Value < (order g)) as nm_bound.
        1, 3: rewrite HeqValue; apply Nat.mod_upper_bound; omega.
        1, 2: remember (BoundRaiseToZ Value).
        1, 2: assert (~(Value > 0)) as ValueNeqGt0.
        1, 3: intros Not; apply n0; [split; omega | rewrite HeqValue; assumption].
        1, 2: apply not_gt, le_n_0_eq in ValueNeqGt0;
          destruct m_bound as [_ m_bound];
          destruct n_bound as [_ n_bound];
          simpl in m_bound;
          simpl in n_bound.
        1: symmetry; apply (mod_squeeze n m (order g)); try omega.
        1: apply (mod_squeeze m n (order g)); try omega.
        (* ugh *)
    - (* surjectivity: *)
      unfold ListSurjective.
      intros h; rewrite filter_In.
      intros [_ h_is_sugroup_mem].
      unfold element_subgroup_mem in h_is_sugroup_mem.
      remember (count_occ eq_dec (iterated_powers G g (S (cardinality G))) h) as q.
      assert (count_occ eq_dec (iterated_powers G g (S (cardinality G))) h > 0)
        as CountGt0.
      destruct q; [contradict h_is_sugroup_mem; discriminate | omega].
      Search (count_occ).
      rewrite <- count_occ_In in CountGt0.
      Search (In _ (iterated_powers _ _ _)).
      rewrite iterated_powers_in in CountGt0.
      destruct CountGt0 as [m [m_bound g_raised_to_m]].
      exists (m mod (order g)).
      Search (0 <= _).
      split.
      * apply in_seq; split; [apply Nat.le_0_l | apply Nat.mod_upper_bound]; omega.
      * rewrite <- power_cycle_mod;
          [assumption | omega | apply element_raised_to_order].
    - (* mapping *)
      intros m m_in_order.
      apply filter_In; split; [apply seq_listing | auto].
      assert (In (g^^m) (iterated_powers G g (S (cardinality G)))) as g_m_in_iterated_powers.
      rewrite iterated_powers_in.
      exists m.
      rewrite in_seq in m_in_order.
      split; [omega  |reflexivity].
      Search (count_occ).
      rewrite (count_occ_In eq_dec) in g_m_in_iterated_powers.
      unfold element_subgroup_mem.
      remember (count_occ eq_dec _ _) as q.
      destruct q; [omega | reflexivity].
  Qed.

  Theorem order_is_cardinality_subgroup (G: finite_group):
    forall (g: G), cardinality_subgroup G (element_subgroup_finite G g) = (order g).
  Proof.
    intros g; symmetry.
    unfold cardinality_subgroup, element_subgroup, subgroup_filter; simpl.
    replace (order g) with (length (seq 0 (order g)));
      [| rewrite seq_length; reflexivity].
    apply (listisomorphism_NoDup_same_length _ _ (fun n => g ^^n));
      [apply power_isomorphism | apply seq_NoDup | apply filter_NoDup, seq_listing].
  Qed.

  Lemma order_divides_group (G: finite_group) : forall g,
      exists k, k * (@order G g) = (cardinality G).
  Proof.
    intros g.
    rewrite <- order_is_cardinality_subgroup.
    exists (length (unique_cosets G (element_subgroup G g))).
    apply (lagrange_theorem G (element_subgroup_finite G g)).
  Qed.
End element_order.

Compute (iterated_powers klein_group k_Y 4).
Compute (@element_power klein_group k_Y 1).
Compute (nth_error (iterated_powers klein_group_finite k_Y 4) 1).
