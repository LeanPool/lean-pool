/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Moments

/-!
# G2Arith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The closed `s`-power evaluation of the `𝒢₂` Step-2 Orlicz scales

ABK26, §4.1, the closed forms the manuscript writes in `e.Xj.Orlicz.bound`
without proof:

```
X_j ≤ 𝒪_{Γ_1}( C K₂ c⋆^{−2} s^{−4} ε^{−2} γ )
    + 𝒪_{Γ_{1/4}}( C K₂ s^{−5} ε^{−2} exp(−C^{−1}c⋆³γ^{−1}) ) .
```

`G2AtomTail.isTwoTermBigOWith_Xcal` produces those two scales as the weighted
penalty *series*

```
Σ_{i ≥ 0} 3^{−¼s(i+1)} (1 + d(i+2)log 3)^k · A ,     k = 1, 4 ,
```

(`xcalScaleOne` and `xcalScaleQuarter` of `G2Moments`).  This module evaluates
both in closed form, at `C(d)·s^{−(k+1)}`: `s^{−2}` at `k = 1` and `s^{−5}` at
`k = 4`.  Since the `Γ_2`-lane per-cube amplitude `A₁` itself carries one power
of `s^{−1}` and enters squared, the composed lane scales are the manuscript's
`s^{−4}` and `s^{−5}`.

This is the `𝒢₂` twin of `RatioTailArith.tsum_weightThird_mul_annulusPenaltyThird_le`
(the `𝒢₀` lane's `γ^{−4}` closed form), and it is not optional: without an
explicit majorant for the two scales the Appendix-D threshold identification of
the lane endpoint cannot be closed at all.

## Route

Three ingredients, exactly as on the `𝒢₀` lane:

* the *penalty bound* `1 + d(i+2)log 3 ≤ (1 + 2d log 3)(i+1)`, so the growing
  lattice-max penalty is a polynomial in the offset at a dimensional constant;
* `(i+1)^k ≤ k!·binom(i+k,k)` and Mathlib's
  `tsum_choose_mul_geometric_of_norm_lt_one k`, giving `k!/(1−w)^{k+1}`;
* the *spectral gap* `1 − 3^{−s/4} ≥ s/8`, valid on the whole standing window
  `s ∈ (0,1]` (the `𝒢₀` lane's version is stated at `γ ≤ 1/4`; the `𝒢₂` lane
  needs it up to `s = 1`, and the same convexity argument delivers it).

Per the elaboration discipline the single transcendental step (the spectral
gap) is confined to an abstract-real private helper and no numeric tactic ever
sees `Real.rpow`, `Real.exp` or `Real.log` applied to a variable.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration

noncomputable section

/-! ## 1. The spectral gap of the `𝒢₂` weight, on the whole window -/

/-- **`1 − 3^{−s/4} ≥ s/8` for `s ∈ (0,1]`.**  The `𝒢₂` lane runs the weight at
rate `¼s` with `s` up to `1`, so the `𝒢₀` lane's `γ ≤ 1/4` version does not
apply; the same convexity chain
`e^{−y} ≤ (1+y)^{−1} ≤ 1 − y/2` (valid for `y ≤ 1`) at `y = ¼s log 3` does. -/
private theorem one_sub_three_rpow_quarter_ge {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) :
    s / 8 ≤ 1 - (3 : ℝ) ^ (-(s / 4)) := by
  have hlog1 : (1 : ℝ) < Real.log 3 := log_three_gt_one
  have hlog2 : Real.log 3 < 2 := log_three_lt_two
  have hy0 : (0 : ℝ) < s / 4 * Real.log 3 := by
    have hq : (0 : ℝ) < s / 4 := by linarith only [h0]
    exact mul_pos hq (by linarith only [hlog1])
  have hy1 : s / 4 * Real.log 3 ≤ 1 := by
    have hq : s / 4 ≤ 1 / 4 := by linarith only [h1]
    have hstep : s / 4 * Real.log 3 ≤ (1 / 4 : ℝ) * 2 :=
      mul_le_mul hq hlog2.le (by linarith only [hlog1]) (by norm_num)
    linarith only [hstep]
  have hrw : (3 : ℝ) ^ (-(s / 4)) = Real.exp (-(s / 4 * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have h1y : (0 : ℝ) < 1 + s / 4 * Real.log 3 := by linarith only [hy0]
  have hexpy : 1 + s / 4 * Real.log 3 ≤ Real.exp (s / 4 * Real.log 3) := by
    linarith only [Real.add_one_le_exp (s / 4 * Real.log 3)]
  have hinv : Real.exp (-(s / 4 * Real.log 3)) ≤ 1 / (1 + s / 4 * Real.log 3) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le h1y hexpy
  have hsq : (s / 4 * Real.log 3) * (s / 4 * Real.log 3) ≤ s / 4 * Real.log 3 := by
    calc (s / 4 * Real.log 3) * (s / 4 * Real.log 3)
        ≤ 1 * (s / 4 * Real.log 3) := mul_le_mul_of_nonneg_right hy1 hy0.le
      _ = s / 4 * Real.log 3 := one_mul _
  have hfrac : 1 / (1 + s / 4 * Real.log 3) ≤ 1 - (s / 4 * Real.log 3) / 2 := by
    rw [div_le_iff₀ h1y]
    have hexpand : (1 - (s / 4 * Real.log 3) / 2) * (1 + s / 4 * Real.log 3)
        = 1 + (s / 4 * Real.log 3) / 2
          - ((s / 4 * Real.log 3) * (s / 4 * Real.log 3)) / 2 := by ring
    rw [hexpand]
    linarith only [hsq]
  have hhalf : s / 8 ≤ (s / 4 * Real.log 3) / 2 := by
    have hstep : s / 4 * 1 ≤ s / 4 * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog1.le (by linarith only [h0])
    linarith only [hstep]
  rw [hrw]
  linarith only [hinv, hfrac, hhalf]

/-! ## 2. The two elementary combinatorial bounds -/

/-- `(i+1) = binom(i+1,1)`: the `k = 1` instance, an identity. -/
private theorem succ_eq_choose_one (i : ℕ) :
    ((i : ℝ) + 1) = ((((i + 1).choose 1 : ℕ)) : ℝ) := by
  rw [Nat.choose_one_right]
  push_cast
  ring

/-- `(i+1)⁴ ≤ 24·binom(i+4,4)`: the `k = 4` instance. -/
private theorem quartic_le_choose (i : ℕ) :
    (((i : ℝ) + 1) ^ (4 : ℕ)) ≤ 24 * ((((i + 4).choose 4 : ℕ)) : ℝ) := by
  have hd : (i + 4).descFactorial 4 = 24 * ((i + 4).choose 4) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    norm_num [Nat.factorial]
  have hval : (i + 4).descFactorial 4 = (i + 1) * ((i + 2) * ((i + 3) * (i + 4))) := by
    have e1 : i + 4 - 3 = i + 1 := by omega
    have e2 : i + 4 - 2 = i + 2 := by omega
    have e3 : i + 4 - 1 = i + 3 := by omega
    have e4 : i + 4 - 0 = i + 4 := by omega
    simp only [Nat.descFactorial, e1, e2, e3, e4, Nat.mul_one]
  have hnat : (i + 1) ^ 4 ≤ 24 * ((i + 4).choose 4) := by
    rw [← hd, hval]
    calc (i + 1) ^ 4 = (i + 1) * ((i + 1) * ((i + 1) * (i + 1))) := by ring
      _ ≤ (i + 1) * ((i + 2) * ((i + 3) * (i + 4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega)
          (Nat.mul_le_mul (by omega) (by omega)))
  have hcast := (Nat.cast_le (α := ℝ)).2 hnat
  push_cast at hcast
  exact hcast

/-! ## 3. The two dimensional constants -/

/-- The dimensional constant of the `Γ_1`-lane closed form. -/
def xcalNormOne (d : ℕ) : ℝ := 64 * (1 + 2 * (d : ℝ) * Real.log 3)

/-- The dimensional constant of the `Γ_{1/4}`-lane closed form. -/
def xcalNormQuarter (d : ℕ) : ℝ := 786432 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)

theorem xcalNormOne_pos (d : ℕ) : 0 < xcalNormOne d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [xcalNormOne]
  positivity

theorem xcalNormQuarter_pos (d : ℕ) : 0 < xcalNormQuarter d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : (0 : ℝ) < 1 + 2 * (d : ℝ) * Real.log 3 := by positivity
  rw [xcalNormQuarter]
  positivity

/-! ## 4. The penalty bound -/

private theorem annulusPenalty_base_le (d : ℕ) (i : ℕ) :
    1 + (d : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) * Real.log 3
      ≤ (1 + 2 * (d : ℝ) * Real.log 3) * ((i : ℝ) + 1) := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hcast : (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hprod : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.log 3 * (i : ℝ) := by positivity
  have hprod2 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 * (i : ℝ) := by positivity
  linarith only [hprod, hprod2, hi]

/-! ## 5. The two closed forms -/

/-- **The `Γ_1`-lane weighted penalty series, in closed form: `C(d)·s^{−2}`.** -/
theorem tsum_weightThird_mul_annulusPenalty_one_le (d : ℕ) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hA : 0 ≤ A) :
    ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * A)
      ≤ xcalNormOne d / s ^ (2 : ℕ) * A := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (-(s / 4)) := Real.rpow_pos_of_pos (by norm_num) _
  have hgap : s / 8 ≤ 1 - (3 : ℝ) ^ (-(s / 4)) := one_sub_three_rpow_quarter_ge hs0 hs1
  have hs8 : (0 : ℝ) < s / 8 := by linarith only [hs0]
  have hw1 : (3 : ℝ) ^ (-(s / 4)) < 1 := by linarith only [hgap, hs8]
  have hnorm : ‖(3 : ℝ) ^ (-(s / 4))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hw0.le]
    exact hw1
  have hB0 : (0 : ℝ) ≤ 1 + 2 * (d : ℝ) * Real.log 3 := by positivity
  have hpen : ∀ p : ℕ, annulusPenalty d 1 p = 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by
    intro p
    have h := annulusPenalty_natPow d (N := 1) (by norm_num) p
    simpa only [Nat.cast_one, inv_one, pow_one] using h
  have hterm : ∀ i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * A)
      ≤ (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
        (((((i + 1).choose 1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) := by
    intro i
    have hwt : weightThird (s / 4) (i + 1)
        = (3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i := by
      rw [weightThird, pow_succ]
      ring
    have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i :=
      mul_nonneg hw0.le (pow_nonneg hw0.le i)
    have hstep : annulusPenalty d 1 (i + 1) * A
        ≤ (1 + 2 * (d : ℝ) * Real.log 3) * ((i : ℝ) + 1) * A := by
      refine mul_le_mul_of_nonneg_right ?_ hA
      rw [hpen]
      exact annulusPenalty_base_le d i
    calc weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * A)
        = ((3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i) *
            (annulusPenalty d 1 (i + 1) * A) := by rw [hwt]
      _ ≤ ((3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i) *
            ((1 + 2 * (d : ℝ) * Real.log 3) * ((i : ℝ) + 1) * A) :=
          mul_le_mul_of_nonneg_left hstep hpow
      _ = (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
            (((i : ℝ) + 1) * ((3 : ℝ) ^ (-(s / 4))) ^ i) := by ring
      _ = (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
            (((((i + 1).choose 1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) := by
          rw [succ_eq_choose_one i]
  have hsumL : Summable fun i : ℕ =>
      weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * A) := by
    have h := summable_weightThird_mul_annulusPenalty d (sprime := s / 4) (A := A)
      (N := 1) (by linarith only [hs0]) (by norm_num) hA
    simpa only [Nat.cast_one, inv_one] using h
  have hsumR : Summable fun i : ℕ =>
      (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
        (((((i + 1).choose 1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
    (summable_choose_mul_geometric_of_norm_lt_one 1 hnorm).mul_left _
  have hconst0 : (0 : ℝ) ≤ A * (1 + 2 * (d : ℝ) * Real.log 3) :=
    mul_nonneg hA hB0
  calc ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d 1 (i + 1) * A)
      ≤ ∑' i : ℕ, (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
          (((((i + 1).choose 1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
        hsumL.tsum_le_tsum hterm hsumR
    _ = (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
          ∑' i : ℕ, (((((i + 1).choose 1 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
        tsum_mul_left
    _ = (A * (1 + 2 * (d : ℝ) * Real.log 3) * (3 : ℝ) ^ (-(s / 4))) *
          (1 / (1 - (3 : ℝ) ^ (-(s / 4))) ^ (1 + 1)) := by
        rw [tsum_choose_mul_geometric_of_norm_lt_one 1 hnorm]
    _ ≤ (A * (1 + 2 * (d : ℝ) * Real.log 3) * 1) * (1 / (s / 8) ^ (1 + 1)) := by
        refine mul_le_mul ?_ ?_
          (div_nonneg zero_le_one (pow_nonneg (by linarith only [hgap, hs8]) _))
          (mul_nonneg hconst0 zero_le_one)
        · exact mul_le_mul_of_nonneg_left hw1.le hconst0
        · refine one_div_le_one_div_of_le (by positivity) ?_
          exact pow_le_pow_left₀ hs8.le hgap (1 + 1)
    _ = xcalNormOne d / s ^ (2 : ℕ) * A := by
        rw [xcalNormOne]
        field_simp
        ring

/-- **The `Γ_{1/4}`-lane weighted penalty series, in closed form: `C(d)·s^{−5}`.** -/
theorem tsum_weightThird_mul_annulusPenalty_quarter_le (d : ℕ) {s A : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hA : 0 ≤ A) :
    ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * A)
      ≤ xcalNormQuarter d / s ^ (5 : ℕ) * A := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (-(s / 4)) := Real.rpow_pos_of_pos (by norm_num) _
  have hgap : s / 8 ≤ 1 - (3 : ℝ) ^ (-(s / 4)) := one_sub_three_rpow_quarter_ge hs0 hs1
  have hs8 : (0 : ℝ) < s / 8 := by linarith only [hs0]
  have hw1 : (3 : ℝ) ^ (-(s / 4)) < 1 := by linarith only [hgap, hs8]
  have hnorm : ‖(3 : ℝ) ^ (-(s / 4))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hw0.le]
    exact hw1
  have hB0 : (0 : ℝ) ≤ (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) := by positivity
  have hpen : ∀ p : ℕ,
      annulusPenalty d (1 / 4) p = (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ^ (4 : ℕ) := by
    intro p
    have h := annulusPenalty_natPow d (N := 4) (by norm_num) p
    have hcast : (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 := by norm_num
    rwa [hcast] at h
  have hterm : ∀ i : ℕ,
      weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * A)
      ≤ (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
        (((((i + 4).choose 4 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) := by
    intro i
    have hwt : weightThird (s / 4) (i + 1)
        = (3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i := by
      rw [weightThird, pow_succ]
      ring
    have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i :=
      mul_nonneg hw0.le (pow_nonneg hw0.le i)
    have hnn : (0 : ℝ) ≤ 1 + (d : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) * Real.log 3 := by
      positivity
    have hbase : annulusPenalty d (1 / 4) (i + 1)
        ≤ (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) * (((i : ℝ) + 1) ^ (4 : ℕ)) := by
      rw [hpen, ← mul_pow]
      exact pow_le_pow_left₀ hnn (annulusPenalty_base_le d i) 4
    have hquart : (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) * (((i : ℝ) + 1) ^ (4 : ℕ))
        ≤ (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) *
          (24 * ((((i + 4).choose 4 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left (quartic_le_choose i) hB0
    have hstep : annulusPenalty d (1 / 4) (i + 1) * A
        ≤ (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) *
            (24 * ((((i + 4).choose 4 : ℕ)) : ℝ)) * A :=
      mul_le_mul_of_nonneg_right (hbase.trans hquart) hA
    calc weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * A)
        = ((3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i) *
            (annulusPenalty d (1 / 4) (i + 1) * A) := by rw [hwt]
      _ ≤ ((3 : ℝ) ^ (-(s / 4)) * ((3 : ℝ) ^ (-(s / 4))) ^ i) *
            ((1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ) *
              (24 * ((((i + 4).choose 4 : ℕ)) : ℝ)) * A) :=
          mul_le_mul_of_nonneg_left hstep hpow
      _ = (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
            (((((i + 4).choose 4 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) := by ring
  have hsumL : Summable fun i : ℕ =>
      weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * A) := by
    have h := summable_weightThird_mul_annulusPenalty d (sprime := s / 4) (A := A)
      (N := 4) (by linarith only [hs0]) (by norm_num) hA
    have hcast : (((4 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / 4 := by norm_num
    rwa [hcast] at h
  have hsumR : Summable fun i : ℕ =>
      (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
        (((((i + 4).choose 4 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
    (summable_choose_mul_geometric_of_norm_lt_one 4 hnorm).mul_left _
  have hconst0 : (0 : ℝ) ≤ A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) :=
    mul_nonneg hA (by positivity)
  calc ∑' i : ℕ, weightThird (s / 4) (i + 1) * (annulusPenalty d (1 / 4) (i + 1) * A)
      ≤ ∑' i : ℕ,
          (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
            (((((i + 4).choose 4 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
        hsumL.tsum_le_tsum hterm hsumR
    _ = (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
          ∑' i : ℕ, (((((i + 4).choose 4 : ℕ)) : ℝ) * ((3 : ℝ) ^ (-(s / 4))) ^ i) :=
        tsum_mul_left
    _ = (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * (3 : ℝ) ^ (-(s / 4))) *
          (1 / (1 - (3 : ℝ) ^ (-(s / 4))) ^ (4 + 1)) := by
        rw [tsum_choose_mul_geometric_of_norm_lt_one 4 hnorm]
    _ ≤ (A * (24 * (1 + 2 * (d : ℝ) * Real.log 3) ^ (4 : ℕ)) * 1) *
          (1 / (s / 8) ^ (4 + 1)) := by
        refine mul_le_mul ?_ ?_
          (div_nonneg zero_le_one (pow_nonneg (by linarith only [hgap, hs8]) _))
          (mul_nonneg hconst0 zero_le_one)
        · exact mul_le_mul_of_nonneg_left hw1.le hconst0
        · refine one_div_le_one_div_of_le (by positivity) ?_
          exact pow_le_pow_left₀ hs8.le hgap (4 + 1)
    _ = xcalNormQuarter d / s ^ (5 : ℕ) * A := by
        rw [xcalNormQuarter]
        field_simp
        ring

/-! ## 6. The two lane scales, in closed form -/

/-- **`xcalScaleOne ≤ C(d)·s^{−2}·A₁²`** — the closed evaluation of the `Γ_1`-lane
Step-2 scale.  Composed with the per-cube amplitude `A₁ ∼ C c⋆^{−1}s^{−1}√γ` of
the anchor this is the manuscript's `C K₂ c⋆^{−2}s^{−4}ε^{−2}γ`. -/
theorem xcalScaleOne_le (d : ℕ) {s A1 : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    xcalScaleOne d s A1
      ≤ gammaTriangleConst 1 * (xcalNormOne d / s ^ (2 : ℕ) * (2 * A1 ^ 2)) := by
  rw [xcalScaleOne]
  refine mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le
  exact tsum_weightThird_mul_annulusPenalty_one_le d hs0 hs1 (by positivity)

/-- **`xcalScaleQuarter ≤ C(d)·s^{−5}·A₂²`** — the closed evaluation of the
`Γ_{1/4}`-lane Step-2 scale, the manuscript's `C K₂
s^{−5}ε^{−2}exp(−C^{−1}c⋆³γ^{−1})` (the per-cube amplitude `A₂` carries no
power of `s`). -/
theorem xcalScaleQuarter_le (d : ℕ) {s A2 : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    xcalScaleQuarter d s A2
      ≤ gammaTriangleConst (1 / 4) * (xcalNormQuarter d / s ^ (5 : ℕ) * (2 * A2 ^ 2)) := by
  rw [xcalScaleQuarter]
  refine mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le
  exact tsum_weightThird_mul_annulusPenalty_quarter_le d hs0 hs1 (by positivity)

end

end Algsuperdiff.Section4.Provider.Proportion
