Require Import List  ListSet Bool FinFun Omega Ring.
Import ListNotations.

Lemma empty_list_not_equal_app (A: Type):
  forall (l1 l2: list A) (a: A), [] <> l1 ++ a :: l2.
Proof.
  induction l1; simpl.
  discriminate.
  intros H; inversion H; intros a0; discriminate.
Qed.

Section hd_error.
  Lemma hd_error_nil: forall A (l: list A), hd_error l = None <-> l = [].
  Proof.
    intros A l.
    compute; destruct l; split; auto; intros H; contradict H; discriminate.
  Qed.

  Lemma hd_error_cons (A: Type): forall l1 (a : A),
      hd_error l1 = Some a <-> exists l2, l1 = a :: l2.
  Proof.
    intros l1 a.
    split.
    - unfold hd_error.
      destruct l1; intros H; auto.
      contradict H; discriminate.
      inversion H; rewrite <- H1; exists l1; reflexivity.
    - intros H; destruct H as [l2 l2_def]; rewrite l2_def; simpl; reflexivity.
  Qed.
End hd_error.

Section In.

  Lemma in_singleton: forall (B: Type) (a b: B), In a [b] <-> a = b.
  Proof.
    split; simpl; intros H; destruct H; auto; tauto.
  Qed.

  Lemma in_not_exists_in_empty_list (A: Type): ~ (exists a : A, In a []).
  Proof.
    intros NonEmpty.
    destruct NonEmpty as [q NonEmpty]; apply in_nil in NonEmpty; auto.
  Qed.

  Lemma in_concat : forall A (l1 l2 : list A) (a b : A),
      In a (l1 ++ l2) -> In a (l1 ++ b :: l2).
  Proof.
    intros A l1 l2 a b.
    induction l1; simpl; intros H; auto.
    destruct H; [left | apply IHl1 in H]; auto.
  Qed.

  Lemma in_not_append (A: Type): forall (l1 l2: list A) a,
      ~ In a l1 -> ~ In a l2 -> ~ In a (l1 ++ l2).
  Proof.
    induction l1; intros l2 b a_not_in_l1 a_not_in_l2.
    - simpl; auto.
    - intros b_in_list.
      apply in_app_or in b_in_list.
      destruct b_in_list as [b_first | b_rest]; auto.
  Qed.

  Lemma in_shuffle : forall A (l1 l2 : list A) (a b : A),
      In a (l1 ++ b :: l2) <-> In a (b :: l1 ++ l2).
    intros A l1 l2 a b.
    induction l1.
    simpl; reflexivity.
    simpl.
    split.
    intros H.
    destruct H; [right; left | auto]; auto.
    rewrite IHl1 in H.
    simpl in H.
    destruct H; auto.
    intros Q.
    destruct Q.
    right; rewrite IHl1, H; simpl; auto.
    destruct H; auto.
    rewrite IHl1.
    right; simpl; right; assumption.
  Qed.
End In.

Section filter.

  Lemma filter_length_equiv: forall (A: Type) g h (l': list A),
      (forall a, g a = h a) -> length (filter g l') = length (filter h l').
  Proof.
    intros B g h l' fn_equiv; induction l'; simpl; auto.
    replace (g a) with (h a); [ | rewrite fn_equiv; reflexivity ].
    destruct (h a); simpl; rewrite IHl'; auto.
  Qed.

  Lemma filter_NotIn : forall (A: Type) f x (l : list A),
      ~In x l -> ~In x (filter f l).
  Proof.
    intros A f x.
    induction l.
    (* base case *)
    simpl; auto.
    (* inductive case *)
    rewrite not_in_cons.
    simpl; destruct (f a); simpl.
    intros [x_not_a H].
    unfold not.
    intros H2.
    destruct H2; auto.
    apply IHl; auto.
    intros [x_not_a H].
    apply IHl; assumption.
  Qed.

  Lemma filter_NoDup :
    forall  (A: Type) f (l: list A), NoDup l -> NoDup (filter f l).
  Proof.
    induction l; auto.
    simpl; auto.
    intros NoDupeList.
    replace (NoDup (a :: l)) with (NoDup ([] ++ a :: l)) in NoDupeList.
    apply NoDup_remove in NoDupeList; simpl in NoDupeList.
    destruct NoDupeList as [NoDup_l a_not_in_l].
    simpl.
    destruct (f a).
    apply NoDup_cons.
    apply filter_NotIn; assumption.
    1-2: apply IHl; assumption.
    simpl; reflexivity.
  Qed.

  (* this makes the next proof slightly nicer ;) *)
  Lemma true_dec : forall b, {b = true} + {b = false}.
    intros b.
    destruct (bool_dec b true); auto.
    apply not_true_is_false in n; auto.
  Qed.

  (* random filter lemmas since the standard lib doesn't have much *)
  Lemma filter_empty_head: forall (A: Type) f (l: list A) a, filter f (a :: l) = [] -> f a <> true.
    intros A f l a.
    intros Filter.
    unfold filter in Filter.
    destruct (bool_dec (f a) true) in Filter.
    rewrite e in Filter; contradict Filter; congruence.
    assumption.
  Qed.

  Lemma filter_empty_rest: forall (A: Type) f (l: list A) a, filter f (a :: l) = [] -> filter f l = [].
    intros A f l a Filter.
    unfold filter in Filter; destruct (f a) in Filter.
    contradict Filter; congruence.
    fold filter in Filter; assumption.
  Qed.

  Lemma filter_head : forall (A: Type) f a (l: list A), f a = true -> filter f (a :: l) = a :: filter f l.
    intros A f a l fa_true.
    unfold filter.
    rewrite fa_true.
    reflexivity.
  Qed.

  Lemma filter_cons : forall (A: Type) f (l1 l2: list A), filter f (l1 ++ l2) = (filter f l1) ++ (filter f l2).
    intros A f.
    induction l1; intros l2.
    repeat rewrite app_nil_r; reflexivity.
    unfold filter.
    destruct (true_dec (f a)) as [Q | Q];
      rewrite <- app_comm_cons;
      rewrite Q;
      fold (filter f (l1 ++ l2));
      fold (filter f l1);
      fold (filter f l2).
    rewrite <- app_comm_cons; congruence.
    congruence.
  Qed.

  Lemma filter_empty: forall (A: Type) f (l: list A), filter f l = [] -> forall a, In a l -> f a <> true.
    intros A f l Filter a.
    intros I.
    apply in_split in I.
    destruct I as [l1 [l2 Q]].
    rewrite Q in Filter.
    rewrite filter_cons in Filter.
    apply app_eq_nil in Filter.
    destruct Filter as [_ filter_fa_nil].
    apply filter_empty_head in filter_fa_nil; assumption.
  Qed.

  Lemma filter_inv : forall A f (l1 l2: list A) a, filter f l1 = a :: l2 -> f a = true. (* /\ l1 = a :: l3 /\ filter f l3 = l2.*)
    intros A f l1 l2 a Filter.
    induction l1.
    (* base case *)
    contradict Filter.
    simpl; congruence.
    (* induction step *)
    simpl in Filter.
    destruct (true_dec (f a0)) as [f_a0_true | f_a0_false] in Filter.
    rewrite f_a0_true in Filter.
    inversion Filter as [e].
    rewrite <- e.
    assumption.
    rewrite f_a0_false in Filter.
    apply IHl1; assumption.
  Qed.

  Lemma filter_bounded (A: Type) (l: list A) f :
    length (filter f l) <= length l.
  Proof.
    induction l; simpl.
    * omega.
    * destruct (f a); simpl; omega.
  Qed.

  Lemma filter_negb (A: Type) (l: list A) f :
    length (filter (fun x => negb (f x)) l) = length l - length (filter f l).
  Proof.
    induction l.
    simpl; reflexivity.
    simpl.
    destruct (true_dec (negb (f a))).
    rewrite negb_true_iff in e.
    rewrite e.
    simpl.
    rewrite IHl.
    fold filter.
    remember (filter_bounded _ l f).
    destruct Heql0.
    destruct (length (filter f l)); omega.
    rewrite e.
    rewrite negb_false_iff in e.
    rewrite e.
    rewrite IHl.
    remember (filter_bounded _ l f).
    destruct Heql0.
    simpl.
    reflexivity.
  Qed.

  Lemma filter_eq (A: Type) (f g: A -> bool) :
    forall l, (forall a, f a = g a) -> filter f l = filter g l.
  Proof.
    induction l; intros fg_equiv; simpl.
    - reflexivity.
    - rewrite fg_equiv, IHl; auto.
  Qed.

  Lemma filter_split: forall (A: Type) (l l': list A) f b,
      filter f l = b :: l' -> exists l2 l3, l = l2 ++ b :: l3 /\ forall b, In b l2 -> f b = false.
  Proof.
    induction l; intros l' f b; simpl; intro filter_eq.
    contradict filter_eq; discriminate.
    destruct (bool_dec (f a) true) as [fa_true | fa_false].
    rewrite fa_true in filter_eq.
    inversion filter_eq as [a_eq_b].
    exists []; exists l; simpl; split; [reflexivity | intros b' H'; contradict H'].
    apply not_true_is_false in fa_false.
    rewrite fa_false in filter_eq.
    apply IHl in filter_eq.
    destruct filter_eq as [l2 [l3 [l_eq l_not_contains]]].
    exists (a :: l2), l3.
    split; [rewrite l_eq; reflexivity | simpl; intros c].
    intros [a_eq_c | c_in_l2]; [rewrite <- a_eq_c | apply l_not_contains]; assumption.
  Qed.
End filter.

Section ListFunctions.
  (* We will use ListInjective rather than Injective for NoDup equality *)

  Definition ListInjective (A B: Type) (f: A -> B) (l: list A) :=
    (forall x y: A, In x l -> In y l -> f x = f y -> x = y).

  Global Arguments ListInjective [A] [B] _ _.

  Lemma injective_implies_listinjective (A B: Type):
    forall (f: A -> B) l, Injective f -> ListInjective f l.
  Proof.
    intros f l Injective.
    unfold ListInjective.
    intros; apply Injective; auto.
  Qed.

  Lemma listinjective_cons (A B: Type):
    forall (f: A -> B) l a, ListInjective f (a::l) -> ListInjective f l.
  Proof.
    intros.
    unfold ListInjective in H.
    unfold ListInjective.
    intros x y x_in y_in.
    apply H; simpl; auto.
  Qed.

  Definition ListSurjective (A B: Type) (f: A -> B) (l: list B) (l': list A) :=
    (forall x: B, In x l -> exists y, In y l' /\ f y = x).

  Global Arguments ListSurjective [A] [B] _ _.

  Lemma listsurjective_cons (A B: Type):
    forall (f: A -> B) l l' a, ListSurjective f (a::l) l' -> ListSurjective f l l'.
  Proof.
    intros.
    unfold ListSurjective in H.
    unfold ListSurjective; intros; apply H; simpl; auto.
  Qed.

  Lemma listsurjective_cons2 (A B: Type):
    forall (f: A -> B) l l' a, ListSurjective f (f a :: l) l' -> ListSurjective f l l'.
  Proof.
    intros f l l' a H.
    unfold ListSurjective.
    intros c c_in.
    apply (H c).
    simpl; auto.
  Qed.

  Lemma listsurjective_incl1 (A B: Type):
    forall (f: A -> B) l xs ys, incl ys xs -> ListSurjective f l ys -> ListSurjective f l xs.
  Proof.
    intros f l xs ys list_incl ys_surjective.
    unfold ListSurjective.
    intros d.
    intros.
    destruct (ys_surjective d) as [q [q_in_y def_q]]; auto.
    exists q.
    split; auto.
  Qed.

  Lemma listsurjective_shows_incl (A B: Type):
    forall (f: A -> B) l1 l2, ListSurjective f l2 l1 -> incl l2 (map f l1).
  Proof.
    intros f l1 l2 Surjective.
    intros d.
    rewrite in_map_iff.
    intros d_in.
    apply (Surjective d) in d_in.
    destruct d_in as [q [def_q q_in]].
    exists q.
    auto.
  Qed.

  Definition ListIsomorphism (A B: Type) (f: A -> B) (l1: list A) (l2: list B) :=
    ListInjective f l1 /\ ListSurjective f l2 l1 /\
    (forall d, In d l1 -> In (f d) l2).

  Global Arguments ListSurjective [A] [B] _ _.
  Global Arguments ListIsomorphism [A] [B] _ _.

End ListFunctions.

Section NoDup.

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

  Lemma NoDup_cons_reduce (A: Type): forall (l: list A) a, NoDup (a :: l) -> NoDup l.
  Proof.
    intros l a.
    rewrite NoDup_cons_iff; tauto.
  Qed.

  Lemma NoDup_listinjection_length_lte : forall A B (l1: list A) (l2: list B) f,
      NoDup l1 ->
      NoDup l2 ->
      ListInjective f l1 ->
      (forall c, In c l1 -> In (f c) l2) ->
      length l1 <= length l2.
  Proof.
    intros A B; induction l1; intros l2 f NoDup_l1 NoDup_l2 f_Injective Injection.
    auto with arith.
    remember (in_eq a l1) as Q.
    destruct HeqQ.
    apply (Injection a) in Q.
    apply in_split in Q.
    destruct Q as [l1' [l3' l2_def]].
    rewrite l2_def.
    replace (length (l1' ++ f a :: l3')) with (S (length (l1' ++ l3'))).
    simpl.
    apply le_n_S.
    apply (IHl1 (l1' ++ l3') f).
    apply NoDup_cons_iff in NoDup_l1; destruct NoDup_l1; auto.
    rewrite l2_def in NoDup_l2; apply NoDup_remove in NoDup_l2.
    destruct NoDup_l2; auto.
    apply (listinjective_cons _ _ _ _ a); auto.
    2: autorewrite with list; simpl; auto with arith.
    (* show if c in l1, then f c is in l1' ++ l3'.  required to apply IH *)
    intros c.
    intros c_in_l1.
    assert (In (f c) l2) as fc_in_l2.
    apply Injection, in_cons; assumption.
    rewrite l2_def in fc_in_l2.
    rewrite in_shuffle in fc_in_l2.
    destruct (in_inv fc_in_l2); [|assumption].
    (* this scenario is impossible because f is injective *)
    apply f_Injective in H; simpl; auto.
    rewrite <- H in c_in_l1.
    apply NoDup_cons_iff in NoDup_l1; destruct NoDup_l1; contradict H0; auto.
  Qed.

  Lemma listsurjective_NoDup_bounds_length (A B: Type):
    forall (f: A -> B) l1 l2, ListSurjective f l2 l1 -> NoDup l2 -> length l2 <= length l1.
  Proof.
    intros f l1 l2 l2_NoDup Surjective.
    replace (length l1) with (length (map f l1)) by apply map_length.
    apply NoDup_incl_length; [ | apply listsurjective_shows_incl]; auto.
  Qed.

  Lemma listisomorphism_NoDup_same_length (A B: Type):
    forall (f: A -> B) l1 l2,
      ListIsomorphism f l1 l2 ->
      NoDup l1 ->
      NoDup l2 ->
      length l1 = length l2.
  Proof.
    intros f l1 l2 [f_Injective [f_Surjective f_Covers]] l1_NoDup l2_NoDup.
    assert (length l1 <= length l2).
    apply (NoDup_listinjection_length_lte _ _ l1 l2 f); auto.
    assert (length l2 <= length l1).
    apply (listsurjective_NoDup_bounds_length _ _ f l1 l2); auto.
    omega.
  Qed.

End NoDup.

Section partition.

  Theorem partition_ind_fst:
    forall (A: Type) f (P : list A -> Prop),
      P [] ->
      (forall a l, f a = true -> P l -> P (a :: l)) ->
      forall l, P (fst (partition f l)).
  Proof.
    intros A f P P_empty P_ind_first.
    induction l; [apply P_empty | auto].
    simpl.
    destruct (partition f l).
    destruct (true_dec (f a)); rewrite e; [apply P_ind_first | auto]; assumption.
  Qed.


  Theorem partition_ind_snd (A: Type) f (P : list A -> Prop) :
      P [] ->
      (forall a l, f a = false -> P l -> P (a :: l)) ->
      forall l, P (snd (partition f l)).
  Proof.
    intros P_empty P_ind_snd.
    induction l; [apply P_empty | auto].
    simpl.
    destruct (partition f l).
    destruct (true_dec (f a)); rewrite e; [auto | apply P_ind_snd]; assumption.
  Qed.

  Lemma partition_fst (A: Type)  (f: A -> bool) (a : A) l :
    In a (fst (partition f l)) -> f a = true.
  Proof.
    apply partition_ind_fst.
    intros in_fst; contradict in_fst; auto.
    intros a0 l0 f_a0 In_a_l0; simpl.
    intros [a_first | a_rest]; [rewrite <- a_first | apply In_a_l0]; assumption.
  Qed.

  Lemma partition_snd (A: Type)  (f: A -> bool) (a : A) l :
    In a (snd (partition f l)) -> f a = false.
  Proof.
    apply partition_ind_snd.
    intros in_snd; contradict in_snd; auto.
    intros a0 l0 f_a0 In_a_l0; simpl.
    intros [a_first | a_rest]; [rewrite <- a_first | apply In_a_l0]; assumption.
  Qed.

End partition.

Section fold_set_add.

  Lemma fold_set_add_in (A: Type) (l: list A) (eq_dec: forall (x y : A), {x = y} + {x <> y}):
    forall c, In c (fold_right (set_add eq_dec) (empty_set A) l) <-> In c l.
  Proof.
    induction l; intros c.
    - simpl; tauto.
    - simpl.
      rewrite set_add_iff.
      split; intros Q; destruct Q; auto; right; apply IHl; auto.
  Qed.

  Lemma fold_set_NoDup (A: Type) (l: list A) (eq_dec: forall (x y : A), {x = y} + {x <> y}):
    NoDup (fold_right (set_add eq_dec) (empty_set A) l).
  Proof.
    induction l.
    - unfold empty_set; simpl; apply NoDup_nil.
    - simpl; apply set_add_nodup; auto.
  Qed.

End fold_set_add.

Section concat.

  Lemma length_concat: forall (B: Type) (l1: list (list B)) m,
      (forall l2, In l2 l1 -> length l2 = m) ->
      length (concat l1) = m * length l1.
  Proof.
    intros B l1 m len_proof.
    induction l1; simpl; auto.
    autorewrite with list.
    rewrite IHl1.
    rewrite len_proof.
    rewrite Nat.mul_succ_r; auto with arith.
    simpl; left; auto.
    intros l0 l0_in_l1; apply len_proof.
    simpl; right; auto.
  Qed.

End concat.


Section concat_map.

  Lemma in_concat_map: forall (A B: Type) (f: A -> list B) b (l: list A),
      In b (concat (map f l)) <-> exists a, In b (f a) /\ In a l.
  Proof.
    intros A B f b.
    induction l; simpl; split.
    - intros H; contradict H; auto.
    - intros H; destruct H; tauto.
    - intros In_b.
      apply in_app_or in In_b.
      destruct In_b as [b_in_f_a | b_in_rest];
        [exists a | apply IHl in b_in_rest; destruct b_in_rest as [d def_d]; exists d];
        tauto.
    - intros [a0 [H1 H2]].
      apply in_or_app.
      destruct H2 as [a_first | a_rest];
        [left; rewrite a_first | right; apply IHl; exists a0]; auto.
  Qed.

End concat_map.

Section fn_partitions.

  Variable (A: Type).
  Variable (f: A -> A).
  Variable (l: list A).
  Variable eq_dec: forall (x y: A), {x = y} + {x <> y}.

  (* TODO: try out a list-based partition, might be less annoying *)
  Inductive fn_partition n :=
  | fn_partition_intro:
      Listing l ->
      (* not sure how to name this condition *)
      (forall x, In x (map f l) -> f x = x) ->
      (forall x, f x = x -> length (filter (fun y => if eq_dec (f y) x then true else false) l) = n) ->
      fn_partition n.

  Definition partition_reprs := fold_right (set_add eq_dec) (empty_set A) (map f l).
  Definition partition_elems a := (filter (fun x => if eq_dec (f x) a then true else false) l).

  Lemma partition_reprs_NoDup: NoDup partition_reprs.
  Proof.
    unfold partition_reprs.
    induction l.
    - unfold empty_set; simpl; apply NoDup_nil.
    - simpl; apply set_add_nodup; auto.
  Qed.

  Lemma partition_reprs_in : forall a, Listing l -> In (f a) partition_reprs.
  Proof.
    intros a Listing.
    unfold partition_reprs.
    rewrite fold_set_add_in.
    apply in_map, Listing.
  Qed.

  Lemma partition_reprs_in2 n: forall d,
      fn_partition n -> In d partition_reprs -> f d = d.
  Proof.
    intros d.
    unfold partition_reprs.
    rewrite fold_set_add_in.
    intros Partition; apply Partition.
  Qed.

  Lemma partition_elems_in : forall a b, In b (partition_elems a) -> f b = a.
  Proof.
    intros a b.
    unfold partition_elems.
    rewrite filter_In.
    destruct (eq_dec (f b) a); auto.
    intros [_ C]; contradict C; congruence.
  Qed.

  Lemma partition_elems_in2: forall a, Listing l -> In a (partition_elems (f a)).
  Proof.
    intros a Listing.
    unfold partition_elems.
    rewrite filter_In.
    split; [apply Listing | destruct (eq_dec (f a) (f a)) ]; auto.
  Qed.

  Lemma partition_elems_NoDup n: forall a, fn_partition n -> NoDup (partition_elems a).
  Proof.
    intros a Partition; apply filter_NoDup.
    apply Partition.
  Qed.

  Lemma partition_elems_length n:
    fn_partition n ->
    forall a, f a = a -> length (partition_elems a) = n.
  Proof.
    intros [_ _ Partition] a.
    unfold partition_elems.
    intros fa_eq_a.
    rewrite <- (Partition a); auto.
  Qed.

  Definition expand_partition :=
    flat_map (fun x => list_prod [x] (partition_elems x)) partition_reprs.

  Definition concat_map_list_prod: forall (B: Type) (l': list B) (f: B -> list B),
      (forall x, NoDup (f x)) -> NoDup l' ->
      NoDup (concat (map (fun x => list_prod [x] (f x)) l')).
  Proof.
    intros B l2 g l1_NoDup l2_NoDup.
    induction l2.
    simpl; apply NoDup_nil.
    simpl.
    autorewrite with list.
    apply NoDup_append.
    - apply Injective_map_NoDup; [intros x y H; inversion H; reflexivity | apply l1_NoDup].
    - apply NoDup_cons_reduce in l2_NoDup; apply IHl2; auto.
    - intros q q_in_map.
      (* first show q has the form (a, d) *)
      (* then use nodup in l2_NoDup *)
      rewrite in_map_iff in q_in_map.
      destruct q_in_map as [d [q_form q_in_ga]].
      rewrite in_concat_map.
      intros [t [t_in_map t_in_l2]].
      rewrite app_nil_r in t_in_map.
      rewrite in_map_iff in t_in_map.
      destruct t_in_map as [u [u_form u_in_gt]].
      rewrite <- u_form in q_form.
      inversion q_form.
      rewrite NoDup_cons_iff in l2_NoDup.
      rewrite H0 in l2_NoDup.
      tauto.
  Qed.

  Theorem expand_partition_NoDup n:
    fn_partition n ->
    NoDup (expand_partition).
  Proof.
    intros Partition.
    unfold expand_partition.
    rewrite flat_map_concat_map.
    apply concat_map_list_prod.
    intros x; apply (partition_elems_NoDup n); auto.
    apply partition_reprs_NoDup.
  Qed.


  Theorem expand_partition_in:
    Listing l ->
    forall c, In c expand_partition <-> (exists d, c = (f d, d)).
  Proof.
    intros Listing c.
    unfold expand_partition.
    rewrite flat_map_concat_map.
    rewrite in_concat_map.
    split.
    - intros [a [a_in_c a_in_reprs]].
      destruct c as (r, s).
      rewrite in_prod_iff in a_in_c.
      elim a_in_c.
      rewrite (in_singleton _ r a).
      intros r_is_a s_in_elem_a.
      apply partition_elems_in in s_in_elem_a.
      exists s.
      rewrite r_is_a, s_in_elem_a.
      reflexivity.
    - intros [d c_has_form].
      exists (f d).
      split; [ | apply partition_reprs_in ]; auto.
      rewrite c_has_form, in_prod_iff.
      split; [ apply in_singleton | apply partition_elems_in2 ]; auto.
  Qed.

  Theorem expand_partition_isomorphism:
    Listing l ->
    ListIsomorphism snd expand_partition l.
  Proof.
    intros Listing.
    try repeat split.
    - unfold ListInjective.
      simple destruct x; simple destruct y; simpl.
      intros a1 a2 H0 H1 H2.
      rewrite <- H2 in H1.
      rewrite expand_partition_in in H0; auto.
      rewrite expand_partition_in in H1; auto.
      (* this is dumb *)
      destruct H0.
      destruct H1.
      inversion H.
      inversion H0.
      rewrite <- H6, <- H4, <- H2.
      reflexivity.
    - unfold ListSurjective.
      intros d d_in_seq.
      exists (pair (f d) d).
      simpl.
      rewrite expand_partition_in; auto.
      split; try exists d; auto.
    - simple destruct d; simpl; intros; apply Listing.
  Qed.

  Theorem expand_partition_same_size n:
    fn_partition n ->
    length expand_partition = length l.
  Proof.
    intros Partition.
    apply (listisomorphism_NoDup_same_length _ _ snd _ l); try apply Partition.
    apply expand_partition_isomorphism; apply Partition.
    apply (expand_partition_NoDup n); auto.
  Qed.

  Theorem expand_partition_length n:
      fn_partition n ->
      length expand_partition = length partition_reprs * n.
  Proof.
    intros Partition.
    unfold expand_partition.
    rewrite flat_map_concat_map.
    rewrite (length_concat _ _ n); auto.
    rewrite map_length; auto with arith.
    intros l2.
    rewrite in_map_iff.
    intros [d [d_form d_in_list]].
    rewrite <- d_form.
    rewrite prod_length.
    rewrite (partition_elems_length n).
    auto with arith.
    apply Partition.
    apply Partition.
    apply (partition_reprs_in2 n) in d_in_list; auto.
    rewrite <- d_in_list.
    apply in_map, Partition.
  Qed.

End fn_partitions.

Section nth_error.

  Lemma nth_error_step (A: Type): forall n (l: list A) a h,
      nth_error (a :: l) (n + 1) = Some h <-> nth_error l n = Some h.
  Proof.
    induction n; induction l; intros b h; simpl.
    * tauto.
    * tauto.
    * destruct n; simpl; tauto.
    * rewrite IHn; tauto.
  Qed.

  Theorem nth_error_Some2 : forall (A: Type) (l : list A) (n : nat) b,
      nth_error l n = Some b -> n < length l.
  Proof.
    intros A l n b.
    remember (nth_error_Some l n) as OtherLemma.
    intros H.
    apply OtherLemma; rewrite H; discriminate.
  Qed.

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

End nth_error.

Section combine.

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
    intros H; simpl; replace (start + 1) with (S start) by omega; rewrite Nat.sub_0_r; reflexivity.
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

  Lemma combine_seq_length (A: Type):
    forall l2 (l: list A)  start len (p: nat * A) l3,
      combine (seq start len) l = l2 ++ p :: l3 -> length l2 = fst p - start.
  Proof.
    induction l2; intros l start len p l3; simpl.
    - intros H; apply combine_seq2 in H; destruct H as [start_eq _];
        rewrite start_eq; auto with arith.
    - intros H.
      assert (combine (seq start len) l = a :: l2 ++ p :: l3) as H' by assumption.
      cut (fst a < fst p).
      intros Cut.
      apply combine_seq2 in H'; destruct H' as [start_eq combine_rest].
      apply IHl2 in combine_rest; rewrite combine_rest.
      omega.
      apply (combine_seq_bound A (l2 ++ p :: l3) l a start len H p).
      rewrite in_app_iff; right; simpl; left; reflexivity.
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
    induction l1; induction l2; intros h j in_hj.
    * rewrite combine_nil in in_hj; contradict in_hj.
    * rewrite combine_nil2 in in_hj; contradict in_hj.
    * rewrite combine_nil in in_hj; contradict in_hj.
    * simpl in in_hj.
      destruct in_hj as [n_eq_0 | n_in_rest].
      - exists 0; inversion n_eq_0 as [[rew1 rew2]].
        rewrite <- rew1, <- rew2; simpl; tauto.
      - apply IHl1 in n_in_rest.
        destruct n_in_rest as [m [rew1 rew2]].
        exists (m + 1).
        split; simpl; rewrite nth_error_step; assumption.
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

End combine.
