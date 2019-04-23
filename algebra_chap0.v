Section Functions.

  Definition injective (A B : Set) (f : A -> B) := forall a a', f a = f a' -> a = a'.

  Definition surjective (A B : Set) (f : A -> B) := forall b, (exists a, f a = b).

  Definition left_inverse (A B : Set) (f : A -> B) (g : B -> A) :=
    forall a, g (f a) = a.

  Definition right_inverse (A B : Set) (f : A -> B) (g : B -> A) :=
    forall b, f (g b) = b.

  Definition nonempty (A : Set) := exists x : A, True.

  Theorem fun_intro (A B : Set) (f : A -> B) : forall a a', a = a' -> f a = f a'.
  Proof.
    intros a a' H; rewrite H; reflexivity.
  Qed.

  Variable (A B : Set).

  Arguments injective {A} {B} _.
  Arguments surjective {A} {B} _.
  Arguments left_inverse {A} {B} _ _.
  Arguments right_inverse {A} {B} _ _.

  Definition partial_inverse (f : A -> B) := B -> option A.
  Definition is_partial_inverse (f : A -> B) (f_inv: partial_inverse f) :=
    forall b a,
      (f_inv b = Some a -> f a = b) /\
      (f_inv b = None -> ~exists a, f a = b).

  Theorem partial_inverse_false (f: A -> B) (f_inv: partial_inverse f) :
    is_partial_inverse f f_inv ->
    forall a, f_inv (f a) = None -> False.
  Proof.
    intros PartialInverse a H.
    remember (f a) as b.
    apply (PartialInverse b a) in H.
    contradict H.
    exists a.
    auto.
  Qed.

  Theorem left_inverse_iff_injective (f : A -> B) (f_inv: partial_inverse f) :
    nonempty A -> is_partial_inverse f f_inv -> (exists g, left_inverse f g) <-> injective f.
  Proof.
    intros [s _] PartialInverse.
    split.
    - intros [g left_inverse] a a' H.
    apply (fun_intro _ _ g (f a) (f a')) in H.
    repeat rewrite left_inverse in H; exact H.
    (* opposite side requires defining a total inverse function
       from the partial inverse *)
    - intros f_injective.
      exists (fun b =>
                match (f_inv b) with
                | Some a => a
                | None => s
                end).
      intros a.
      remember (f_inv (f a)) as Q.
      symmetry in HeqQ.
      destruct Q.
      apply (PartialInverse (f a)) in HeqQ.
      apply f_injective in HeqQ.
      exact HeqQ.
      apply (partial_inverse_false _ _ PartialInverse) in HeqQ.
      contradict HeqQ.
  Qed.

  Theorem right_inverse_iff_surjective (f : A -> B) (f_inv: partial_inverse f):
    nonempty A -> is_partial_inverse f f_inv -> (exists g, right_inverse f g) <-> surjective f.
  Proof.
    intros [s _] PartialInverse.
    split.
    - intros [g right_inverse].
      unfold surjective.
      intros b; exists (g b).
      rewrite right_inverse; reflexivity.
    - intros f_surjective.
      unfold right_inverse.
      exists (fun b => match (f_inv b) with | Some a => a | None => s end).
      intros b.
      remember (f_inv b) as Q.
      symmetry in HeqQ.
      destruct Q.
      apply (PartialInverse) in HeqQ.
      exact HeqQ.
      apply (PartialInverse _ s) in HeqQ.
      contradict HeqQ.
      apply f_surjective.
  Qed.
End Functions.
