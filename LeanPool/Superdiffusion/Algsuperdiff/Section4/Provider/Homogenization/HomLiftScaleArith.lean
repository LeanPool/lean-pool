/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Log
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# HomLiftScaleArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the triadic scale arithmetic of the Hölder
# lifting

This module isolates the three purely arithmetic ingredients of the Step-3c
bridge

```text
  3^{-m} ‖u - v‖_{L^∞(□_m)} ≤ C 3^{-ms} ‖∇u - ∇v‖_{W_hat^{-s,∞}(□_m)},
```

read through the `(∞,∞)`-index
Hölder lifting: a negative-order bound on `∇w` at exponent `-s` lifts to the
`C^{0,1-s}` seminorm of `w`, which is stronger than `L^∞`.  The three
ingredients are

* `exists_triadic_scale` — for `0 < t ≤ 3^m` there is a triadic scale
  `n ≤ m` with `3^n ≤ t < 3^{n+1}`.  This is the scale at which the
  telescoping argument is cut.
* `liftGeomFactor s = (1 - 3^{-(1-s)})⁻¹` — the geometric factor of the
  telescoping sum over the scales below `n`, together with the bound
  `liftGeomFactor s ≤ 3` valid on the whole range `0 < s ≤ 1/2`.
* `three_rpow_le_two` — `3^s ≤ 2` on `0 ≤ s ≤ 1/2`, the factor lost when the
  Lipschitz term of the regularization is converted into a `t^{1-s}` term.

**The `s`-dependence.**  Both constants are bounded *uniformly* on
`s ∈ (0,1/2]`; neither carries a `(1-s)^{-1}` factor there.  The blow-up of
`liftGeomFactor` is at the endpoint `s → 1`, which this development never
approaches: the §4.5 parameter selection pins
`s = |log γ|⁻¹`, and Step 3 additionally records `s < 1/10` for small `γ`.  So the lifting's constant is absolutely bounded at the pin and
nothing has to be absorbed by the `E_{ThmB}(m)` budget.

## References

* ABK26, Theorem B Step 3 (the bridge display).
* ABK26 (the introduction's `W^{-s,∞} ↔ Hölder` remark) and
  (`[·]_{C^{0,s}}` vs `[·]_{W^{s,∞}}`).
-/

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

/-! ## 1. Powers of three: `zpow` versus `rpow` -/

/-- The base `3` used by `Int.log` is the natural-number literal; this is its
identification with the real literal. -/
theorem natCast_three : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num

/-- A real power of `3` at an integer exponent is the corresponding `zpow`. -/
theorem three_rpow_intCast (n : ℤ) : (3 : ℝ) ^ ((n : ℤ) : ℝ) = ((3 : ℕ) : ℝ) ^ (n : ℤ) := by
  rw [natCast_three, Real.rpow_intCast]

theorem three_rpow_pos (t : ℝ) : (0 : ℝ) < (3 : ℝ) ^ t :=
  Real.rpow_pos_of_pos (by norm_num) t

theorem three_rpow_nonneg (t : ℝ) : (0 : ℝ) ≤ (3 : ℝ) ^ t :=
  (three_rpow_pos t).le

/-- Real powers of `3` are monotone in the exponent. -/
theorem three_rpow_le_three_rpow {a b : ℝ} (hab : a ≤ b) :
    (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) hab

/-! ## 2. Triadic scale selection -/

/-- **The scale cut.**  For `0 < t ≤ 3^m` there is a triadic scale `n ≤ m`
with `3^n ≤ t < 3^{n+1}`.

This is the scale at which the telescoping Hölder argument is cut: below `n`
one uses the approximation estimate, at `n` the Lipschitz estimate. -/
theorem exists_triadic_scale {t : ℝ} (ht : 0 < t) {m : ℤ}
    (htm : t ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ)) :
    ∃ n : ℤ, n ≤ m ∧ (3 : ℝ) ^ ((n : ℤ) : ℝ) ≤ t ∧ t < (3 : ℝ) ^ (((n + 1 : ℤ) : ℤ) : ℝ) := by
  refine ⟨Int.log 3 t, ?_, ?_, ?_⟩
  · have hmono : Int.log 3 t ≤ Int.log 3 (((3 : ℕ) : ℝ) ^ (m : ℤ)) := by
      refine Int.log_mono_right ht ?_
      rw [← three_rpow_intCast m]
      exact htm
    rwa [Int.log_zpow (by norm_num : 1 < 3)] at hmono
  · rw [three_rpow_intCast]
    exact Int.zpow_log_le_self (by norm_num : 1 < 3) ht
  · rw [three_rpow_intCast]
    exact Int.lt_zpow_succ_log_self (by norm_num : 1 < 3) t

/-! ## 3. The two absolute constants -/

/-- `3^{1/2} ≥ 3/2`. -/
theorem three_rpow_half_ge : (3 : ℝ) / 2 ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) := by
  by_contra hcon
  push Not at hcon
  have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) := three_rpow_nonneg _
  have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) < ((3 : ℝ) / 2) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hcon h0 (by norm_num)
  have he : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [he] at hsq
  norm_num at hsq

/-- `3^{1/2} ≤ 2`. -/
theorem three_rpow_half_le_two : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hsq : (2 : ℝ) ^ (2 : ℕ) < ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hcon (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)
  have he : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [he] at hsq
  norm_num at hsq

/-- **`3^s ≤ 2` on `0 ≤ s ≤ 1/2`** — the factor lost when the Lipschitz term
of the scale-`n` regularization is converted into a `t^{1-s}` term. -/
theorem three_rpow_le_two {s : ℝ} (hs : s ≤ 1 / 2) : (3 : ℝ) ^ s ≤ 2 :=
  (three_rpow_le_three_rpow hs).trans three_rpow_half_le_two

/-- **The telescoping geometric factor** `(1 - 3^{-(1-s)})⁻¹`, the sum of the
geometric series `∑_{k≥0} 3^{-k(1-s)}` governing the increments of the
regularization family below a given scale. -/
def liftGeomFactor (s : ℝ) : ℝ := (1 - (3 : ℝ) ^ (-(1 - s)))⁻¹

theorem liftGeomFactor_def (s : ℝ) : liftGeomFactor s = (1 - (3 : ℝ) ^ (-(1 - s)))⁻¹ := rfl

/-- On `s ≤ 1/2` the geometric ratio is at most `2/3`. -/
theorem three_rpow_neg_one_sub_le {s : ℝ} (hs : s ≤ 1 / 2) :
    (3 : ℝ) ^ (-(1 - s)) ≤ 2 / 3 := by
  have hexp : -(1 - s) ≤ -((1 : ℝ) / 2) := by linarith only [hs]
  have hmono : (3 : ℝ) ^ (-(1 - s)) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2)) :=
    three_rpow_le_three_rpow hexp
  have hinv : (3 : ℝ) ^ (-((1 : ℝ) / 2)) = ((3 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hle : ((3 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ ≤ ((3 : ℝ) / 2)⁻¹ :=
    inv_anti₀ (by norm_num) three_rpow_half_ge
  calc (3 : ℝ) ^ (-(1 - s)) ≤ ((3 : ℝ) ^ ((1 : ℝ) / 2))⁻¹ := by rw [← hinv]; exact hmono
    _ ≤ ((3 : ℝ) / 2)⁻¹ := hle
    _ = 2 / 3 := by norm_num

theorem one_sub_three_rpow_pos {s : ℝ} (hs : s < 1) :
    (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - s)) := by
  have hlt : (3 : ℝ) ^ (-(1 - s)) < (3 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hs])
  rw [Real.rpow_zero] at hlt
  linarith only [hlt]

theorem liftGeomFactor_pos {s : ℝ} (hs : s < 1) : 0 < liftGeomFactor s :=
  inv_pos.mpr (one_sub_three_rpow_pos hs)

theorem liftGeomFactor_nonneg {s : ℝ} (hs : s < 1) : 0 ≤ liftGeomFactor s :=
  (liftGeomFactor_pos hs).le

/-- **The `s`-dependence of the lifting.**  On the whole range
`s ≤ 1/2` — in particular at the §4.5 pin `s = |log γ|⁻¹`, and a fortiori
under Step 3's own `s < 1/10` — the telescoping factor is bounded by the
absolute constant `3`.  No `(1-s)^{-1}` factor is incurred. -/
theorem liftGeomFactor_le_three {s : ℝ} (hs : s ≤ 1 / 2) : liftGeomFactor s ≤ 3 := by
  have hs1 : s < 1 := by linarith only [hs]
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - s)) := one_sub_three_rpow_pos hs1
  have hratio : (3 : ℝ) ^ (-(1 - s)) ≤ 2 / 3 := three_rpow_neg_one_sub_le hs
  have hthird : (1 : ℝ) / 3 ≤ 1 - (3 : ℝ) ^ (-(1 - s)) := by linarith only [hratio]
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 3) hthird
  rw [liftGeomFactor_def]
  calc (1 - (3 : ℝ) ^ (-(1 - s)))⁻¹ = 1 / (1 - (3 : ℝ) ^ (-(1 - s))) := by rw [one_div]
    _ ≤ 1 / (1 / 3) := this
    _ = 3 := by norm_num

/-- Descending `j` triadic scales multiplies the weight `3^{ac}` by the `j`-th
power of the geometric ratio `3^{-c}`.  This is the identity that turns the
scale-indexed increment estimate into a geometric series. -/
theorem three_rpow_sub_natCast_mul (a c : ℝ) (j : ℕ) :
    (3 : ℝ) ^ ((a - (j : ℝ)) * c) = (3 : ℝ) ^ (a * c) * ((3 : ℝ) ^ (-c)) ^ j := by
  have h1 : ((3 : ℝ) ^ (-c)) ^ j = (3 : ℝ) ^ (-c * (j : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-c)) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## 4. Geometric sums -/

/-- The finite geometric sums of the ratio `3^{-(1-s)}` are bounded by
`liftGeomFactor s`. -/
theorem geom_sum_three_rpow_le {s : ℝ} (hs : s < 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, ((3 : ℝ) ^ (-(1 - s))) ^ i) ≤ liftGeomFactor s := by
  set r : ℝ := (3 : ℝ) ^ (-(1 - s)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := three_rpow_nonneg _
  have hpos : (0 : ℝ) < 1 - r := one_sub_three_rpow_pos hs
  have hr1 : r < 1 := by linarith only [hpos]
  have hne : r ≠ 1 := by linarith only [hr1]
  have hsum : (∑ i ∈ Finset.range k, r ^ i) = (1 - r ^ k) / (1 - r) := by
    rw [geom_sum_eq hne, show (1 : ℝ) - r ^ k = -(r ^ k - 1) by ring,
      show (1 : ℝ) - r = -(r - 1) by ring, neg_div_neg_eq]
  have hpowk : (0 : ℝ) ≤ r ^ k := pow_nonneg hr0 k
  rw [hsum, liftGeomFactor_def, ← hrdef, ← one_div]
  exact div_le_div_of_nonneg_right (by linarith only [hpowk]) hpos.le

end

end Algsuperdiff.Section4.Provider.Homogenization
