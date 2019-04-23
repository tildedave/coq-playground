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

  Theorem left_inverse_implies_injective (f : A -> B) :
    nonempty A -> (exists g, left_inverse f g) -> injective f.
  Proof.
    intros [s _] [g left_inverse].
    unfold injective.
    intros a a' H.
    apply (fun_intro _ _ g (f a) (f a')) in H.
    repeat rewrite left_inverse in H; exact H.
    (* opposite side requires defining an inverse function,
       need to make f range decidable for this *)
  Qed.

  Theorem right_inverse_implies_surjective (f : A -> B):
    nonempty A -> (exists g, right_inverse f g) -> surjective f.
  Proof.
    intros _ [g right_inverse].
    unfold surjective.
    intros b; exists (g b).
    rewrite right_inverse; reflexivity.
  Qed.

End Functions.
