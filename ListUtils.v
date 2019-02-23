Require Import List Bool FinFun.
Import ListNotations.

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
End filter.

Section NoDup.
  Lemma NoDup_injection_length_lte : forall A B (l1: list A) (l2: list B) f,
      NoDup l1 ->
      NoDup l2 ->
      Injective f ->
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
    Search (_ <= _ -> S _ <= S _).
    apply le_n_S.
    apply (IHl1 (l1' ++ l3') f).
    apply NoDup_cons_iff in NoDup_l1; destruct NoDup_l1; auto.
    rewrite l2_def in NoDup_l2; apply NoDup_remove in NoDup_l2.
    destruct NoDup_l2; auto.
    assumption.
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
    apply f_Injective in H.
    rewrite <- H in c_in_l1.
    apply NoDup_cons_iff in NoDup_l1; destruct NoDup_l1; contradict H0; auto.
  Qed.

  Lemma NoDup_injection_length : forall A B (l1: list A) (l2: list B) f f_inv,
      NoDup l1 ->
      NoDup l2 ->
      Injective f ->
      Injective f_inv ->
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
    apply (NoDup_injection_length_lte _ _ l1 l2 f); auto.
    intros; apply Injection; auto.
    apply (NoDup_injection_length_lte _ _ l2 l1 f_inv); auto.
    intros; apply Injection; auto.
    rewrite f_Inverse; auto.
  (* we need to apply the reverse of f, but I'm not sure how to do that
       because of the universe mismatch *)
  Qed.

End NoDup.
