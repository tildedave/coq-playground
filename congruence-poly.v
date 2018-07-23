Require Import ZArith BinIntDef.

Local Open Scope Z_scope.

Theorem poly_congruence_pg_28 : ~(exists x, x * x - 117 * x + 31 = 0).
Proof.
  assert (Zodd (-117)) as H117IsOdd. compute. auto.
  assert (Zodd 31) as H31IsOdd. compute. auto.
  intro H.
  destruct H as [x H].
  destruct (Zeven_odd_dec x) as [HXIsEven | HXIsOdd].
  - assert (Zeven (x * x)) as HXSquaredIsEven. apply (Zeven_mult_Zeven_l x x HXIsEven).
    assert (Zeven (-117 * x)) as HLinearTermIsEven. apply (Zeven_mult_Zeven_r (-117) x HXIsEven).
    assert (HPolyIsOdd := HXSquaredIsEven).
    apply (Zeven_plus_Zeven _ _ HLinearTermIsEven) in HPolyIsOdd.
    apply (Zodd_plus_Zeven _ _ H31IsOdd) in HPolyIsOdd.
    replace (31 + (-117 * x + x * x)) with (x * x - 117 * x + 31) in HPolyIsOdd.
    rewrite H in HPolyIsOdd. compute in HPolyIsOdd. assumption. ring.
  - assert (Zodd (x * x)) as HXSquaredIsOdd. apply (Zodd_mult_Zodd x x HXIsOdd HXIsOdd).
    assert (Zodd (-117 * x)) as HLinearTermIsOdd. apply (Zodd_mult_Zodd (-117) x H117IsOdd HXIsOdd).
    assert (HPolyIsOdd := HXSquaredIsOdd).
    apply (Zodd_plus_Zodd _ _ HLinearTermIsOdd) in HPolyIsOdd.
    apply (Zodd_plus_Zeven _ _ H31IsOdd) in HPolyIsOdd.
    replace (31 + (-117 * x + x * x)) with (x * x - 117 * x + 31) in HPolyIsOdd.
    rewrite H in HPolyIsOdd. compute in HPolyIsOdd. assumption. ring.
Qed.

Theorem poly_congruence_pg_28_cleaner : ~(exists x, x * x - 117 * x + 31 = 0).
Proof.
  assert (Zodd (-117)) as H117IsOdd. compute. auto.
  assert (Zodd 31) as H31IsOdd. compute. auto.
  intro H.
  destruct H as [x H].
  assert (Zeven (-117 * x + x * x)) as HVariableComboIsEven.
  destruct (Zeven_odd_dec x) as [HXIsEven | HXIsOdd].
  - assert (Zeven (x * x)) as HXSquaredIsEven. apply (Zeven_mult_Zeven_l x x HXIsEven).
    assert (Zeven (-117 * x)) as HLinearTermIsEven. apply (Zeven_mult_Zeven_r (-117) x HXIsEven).
    apply (Zeven_plus_Zeven _ _ HLinearTermIsEven) in HXSquaredIsEven.
    assumption.
  - assert (Zodd (x * x)) as HXSquaredIsOdd. apply (Zodd_mult_Zodd x x HXIsOdd HXIsOdd).
    assert (Zodd (-117 * x)) as HLinearTermIsOdd. apply (Zodd_mult_Zodd (-117) x H117IsOdd HXIsOdd).
    apply (Zodd_plus_Zodd _ _ HLinearTermIsOdd) in HXSquaredIsOdd.
    assumption.
  - apply (Zodd_plus_Zeven _ _ H31IsOdd) in HVariableComboIsEven.
    replace (31 + (-117 * x + x * x)) with (x * x - 117 * x + 31) in HVariableComboIsEven.
    rewrite H in HVariableComboIsEven.
    compute in HVariableComboIsEven. contradict HVariableComboIsEven.
    ring.
Qed.
