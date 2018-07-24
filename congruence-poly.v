Require Import ZArith BinIntDef.

Local Open Scope Z_scope.

Theorem poly_congruence_pg_28 : ~(exists x, x * x - 117 * x + 31 = 0).
Proof.
  (** First establish that the constants we use (-117 and 31) are odd. *)
  assert (Zodd (-117)) as H117IsOdd. compute. auto.
  assert (Zodd 31) as H31IsOdd. compute. auto.
  (** We proceed with a proof by contradiction.  Support some x exists.  Then x^2 - 117*x must be even.  Therefore the polynomial is odd, and the result can cannot be zero. *)
  intro H.
  destruct H as [x H].
  (** We show a slightly different term is even because it makes the proof more straightforward. *)
  assert (Zeven (-117 * x + x * x)) as HVariableComboIsEven.
  (** We proceed by the case of whether x is even or odd. *)
  destruct (Zeven_odd_dec x) as [HXIsEven | HXIsOdd].
  (** If x is even, both x^2 and -117 * x must be even.  The sum of two evens is also even. **)
  - assert (Zeven (x * x)) as HXSquaredIsEven. apply (Zeven_mult_Zeven_l x x HXIsEven).
    assert (Zeven (-117 * x)) as HLinearTermIsEven. apply (Zeven_mult_Zeven_r (-117) x HXIsEven).
    apply (Zeven_plus_Zeven _ _ HLinearTermIsEven) in HXSquaredIsEven.
    assumption.
  (** If x is even, both x^2 and -117 * x must be odd.  The sum of two odds is also odd. **)
  - assert (Zodd (x * x)) as HXSquaredIsOdd. apply (Zodd_mult_Zodd x x HXIsOdd HXIsOdd).
    assert (Zodd (-117 * x)) as HLinearTermIsOdd. apply (Zodd_mult_Zodd (-117) x H117IsOdd HXIsOdd).
    apply (Zodd_plus_Zodd _ _ HLinearTermIsOdd) in HXSquaredIsOdd.
    assumption.
    (** Since the term x^2 + -117 * x) is even, the sum of it with 31 must be odd.
        However 0 cannot be odd, so there cannot be an x that relationship x^2 - 117 * x + 31. *)
  - apply (Zodd_plus_Zeven _ _ H31IsOdd) in HVariableComboIsEven.
    replace (31 + (-117 * x + x * x)) with (x * x - 117 * x + 31) in HVariableComboIsEven.
    rewrite H in HVariableComboIsEven.
    compute in HVariableComboIsEven. contradict HVariableComboIsEven.
    (** The replacement we used is easily proven with the ring tactic. *)
    ring.
Qed.
