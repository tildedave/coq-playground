Require Import List  ListSet Bool FinFun Omega.
Import ListNotations.

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

  Lemma in_concat : forall A (l1 l2 : list A) (a b : A),
      In a (l1 ++ l2) -> In a (l1 ++ b :: l2).
  Proof.
    intros A l1 l2 a b.
    induction l1; simpl; intros H; auto.
    destruct H; [left | apply IHl1 in H]; auto.
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
  Admitted.

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

  Lemma listsurjective_shows_length (A B: Type):
    forall (f: A -> B) l1 l2, ListSurjective f l2 l1 -> NoDup l2 -> length l2 <= length l1.
  Proof.
    intros f l1 l2 l2_NoDup Surjective.
    replace (length l1) with (length (map f l1)) by apply map_length.
    apply NoDup_incl_length; [ | apply listsurjective_shows_incl]; auto.
  Qed.

  Definition ListIsomorphism (A B: Type) (f: A -> B) (l1: list A) (l2: list B) :=
    ListInjective f l1 /\ ListSurjective f l2 l1.

  Global Arguments ListSurjective [A] [B] _ _.

End ListFunctions.

Section NoDup.

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
    intros A B l1.
    induction l1.
    intros; auto with arith.
    intros l2 f NoDup_l1 NoDup_l2 f_Injective Injection.
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
    destruct (in_inv fc_in_l2).
    (* this scenario is impossible because f is injective *)
    Focus 2. assumption.
    apply f_Injective in H; simpl; auto.
    rewrite <- H in c_in_l1.
    apply NoDup_cons_iff in NoDup_l1; destruct NoDup_l1; contradict H0; auto.
  Qed.

  Lemma NoDup_listinjection_length : forall A B (l1: list A) (l2: list B) f f_inv,
      NoDup l1 ->
      NoDup l2 ->
      ListInjective f l1 ->
      ListInjective f_inv l2 ->
      (forall c, In c l1 <-> In (f c) l2) ->
      (forall d, In d l2 <-> In (f_inv d) l1) ->
      (forall e, f (f_inv e) = e) ->
      length l1 = length l2.
  Proof.
    intros A B l1 l2 f f_inv NoDup_l1 NoDup_l2 f_Injective f_inv_Injective
           Injection InverseInjection f_Inverse.
    cut (length l1 <= length l2).
    cut (length l2 <= length l1).
    intros; auto with arith.
    Focus 2.
    apply (NoDup_listinjection_length_lte _ _ l1 l2 f); auto.
    intros; apply Injection; auto.
    apply (NoDup_listinjection_length_lte _ _ l2 l1 f_inv); auto.
    intros; apply Injection; auto.
    rewrite f_Inverse; auto.
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
