(* Originally from https://raw.githubusercontent.com/tchajed/strong-induction/master/StrongInduction.v *)

(** Here we prove the principle of strong induction, induction on the natural
numbers where the inductive hypothesis includes all smaller natural numbers. *)

Require Import PeanoNat.

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.

Tactic Notation "strong" "induction" ident(n) := induction n using strong_induction.