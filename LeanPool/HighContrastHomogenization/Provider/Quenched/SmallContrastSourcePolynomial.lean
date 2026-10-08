/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceScaleMinimal
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapSmallness
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSourcePolynomial

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source constants are polynomial in the growth bar

`hentry` needs an **upper** bound on `3 ^ N1`, where
`N1 = sK + 1 + gap`, and every factor of it must end up polynomial in the base
`2 + aspectRatio Ebase * Kbase` so's base-uniform machinery can convert it
into a law-free exponent.

Three of the factors were already available; this file supplies the rest:

* the `ℤ`-ceiling companion of's `three_pow_ceil_logb_le`, and with it a
  **minimal** gap — `exists_gap_three_pow_le_minimal` gives existence only, exactly as
  `exists_source_scale_minimal` did, and for the same reason that is not enough;
* `sourceMomentOne` and `sourceMomentSix` against a power of the growth bar,
  the only obstacle being the `Real.log` inside them, which `log x ≤ x - 1`
  removes;
* `badSourceConstant` against `sourceMomentSix`, where the fractional powers are
  absorbed by `y ^ c ≤ 1 + y` for `c ∈ [0,1]`.

Together with `growthBar K ≤ 2 + aspectRatio E * K` these put every
source constant under a power of the base.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-! ## The `ℤ`-ceiling device, and a minimal gap -/

/-- The `ℤ`-ceiling companion of `three_pow_ceil_logb_le`. -/
theorem three_zpow_ceil_logb_le {x : ℝ} (hx : 0 < x) :
    (3 : ℝ) ^ (⌈Real.logb 3 x⌉ : ℤ) ≤ 3 * x := by
  have hlt : ((⌈Real.logb 3 x⌉ : ℤ) : ℝ) < Real.logb 3 x + 1 :=
    Int.ceil_lt_add_one _
  have hstep : (3 : ℝ) ^ (((⌈Real.logb 3 x⌉ : ℤ) : ℝ)) ≤
      (3 : ℝ) ^ (Real.logb 3 x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
  rw [Real.rpow_intCast] at hstep
  have hval : (3 : ℝ) ^ (Real.logb 3 x + 1) = x * 3 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx,
      Real.rpow_one]
  rw [hval] at hstep
  linarith only [hstep]

/-- **The gap, chosen minimally.**  `exists_gap_three_pow_le_minimal` gives a gap
that pushes the adapter error below tolerance; `hentry` also needs to know the
gap is not much larger than the ratio it is built from. -/
theorem exists_gap_three_pow_le_minimal {A sigma : ℝ} (hA : 0 < A)
    (hsigma : 0 < sigma) :
    ∃ gap : ℤ, 1 ≤ gap ∧ A * (3 : ℝ) ^ (-(gap : ℝ)) ≤ sigma ∧
      (3 : ℝ) ^ gap ≤ 3 * max 1 (A / sigma) := by
  have hratio : 0 < A / sigma := div_pos hA hsigma
  set c : ℤ := ⌈Real.logb 3 (A / sigma)⌉ with hc
  set gap : ℤ := max 1 c with hgap
  have hgap1 : 1 ≤ gap := le_max_left _ _
  set z : ℝ := (3 : ℝ) ^ gap with hz
  have hz0 : (0 : ℝ) < z := by rw [hz]; positivity
  have hcgap : ((c : ℤ) : ℝ) ≤ ((gap : ℤ) : ℝ) := by
    rw [hgap]; exact_mod_cast le_max_right 1 c
  have hratz : A / sigma ≤ z := by
    have h1 : Real.logb 3 (A / sigma) ≤ ((gap : ℤ) : ℝ) := by
      have := Int.le_ceil (Real.logb 3 (A / sigma))
      rw [← hc] at this
      linarith only [this, hcgap]
    have hstep : (3 : ℝ) ^ (Real.logb 3 (A / sigma)) ≤
        (3 : ℝ) ^ (((gap : ℤ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hratio,
      Real.rpow_intCast, ← hz] at hstep
  refine ⟨gap, hgap1, ?_, ?_⟩
  · have hzeq : (3 : ℝ) ^ (-((gap : ℤ) : ℝ)) = z⁻¹ := by
      rw [hz, ← Real.rpow_intCast (3 : ℝ) gap,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    rw [hzeq, mul_inv_le_iff₀ hz0]
    have h := (div_le_iff₀ hsigma).mp hratz
    linarith only [h]
  · have hmax1 : (1 : ℝ) ≤ max 1 (A / sigma) := le_max_left _ _
    rcases le_total c 1 with hle | hle
    · have hg1 : gap = 1 := by rw [hgap]; exact max_eq_left hle
      rw [hg1, zpow_one]
      linarith only [hmax1]
    · have hgc : gap = c := by rw [hgap]; exact max_eq_right hle
      rw [hgc, hc]
      refine le_trans (three_zpow_ceil_logb_le hratio) ?_
      have hmr : A / sigma ≤ max 1 (A / sigma) := le_max_right _ _
      linarith only [hmr]

/-! ## Removing the logarithm -/

/-- A fractional power is below `1 + y`. -/
theorem rpow_le_one_add {y c : ℝ} (hy : 0 ≤ y) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    y ^ c ≤ 1 + y := by
  rcases le_total y 1 with hle | hle
  · have h : y ^ c ≤ (1 : ℝ) ^ c := Real.rpow_le_rpow hy hle hc0
    rw [Real.one_rpow] at h
    linarith only [h, hy]
  · have h : y ^ c ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hle hc1
    rw [Real.rpow_one] at h
    linarith only [h]

/-! ## The source moments against a power of the growth bar -/

theorem sourceMomentOne_le (K : ℝ) :
    sourceMomentOne K ≤
      3 * growthBar K ^ (IndependentSums.natTriangular 1 + 1) := by
  have hG2 : (2 : ℝ) ≤ growthBar K := le_max_left 2 K
  have hG0 : (0 : ℝ) < growthBar K := by linarith only [hG2]
  have hlog : Real.log (growthBar K) ≤ growthBar K - 1 :=
    Real.log_le_sub_one_of_pos hG0
  have hpow0 : (0 : ℝ) ≤ growthBar K ^ IndependentSums.natTriangular 1 := by
    positivity
  have hone : (1 : ℝ) ≤ growthBar K ^ (IndependentSums.natTriangular 1 + 1) :=
    one_le_pow₀ (by linarith only [hG2])
  have hsucc : growthBar K ^ (IndependentSums.natTriangular 1 + 1) =
      growthBar K ^ IndependentSums.natTriangular 1 * growthBar K := by
    rw [pow_succ]
  rw [sourceMomentOne]
  nlinarith only [hlog, hpow0, hone, hsucc.le, hsucc.ge, hG0, hG2]

theorem sourceMomentSix_le (K : ℝ) :
    sourceMomentSix K ≤
      13 * growthBar K ^ (IndependentSums.natTriangular 6 + 1) := by
  have hG2 : (2 : ℝ) ≤ growthBar K := le_max_left 2 K
  have hG0 : (0 : ℝ) < growthBar K := by linarith only [hG2]
  have hlog : Real.log (growthBar K) ≤ growthBar K - 1 :=
    Real.log_le_sub_one_of_pos hG0
  have hpow0 : (0 : ℝ) ≤ growthBar K ^ IndependentSums.natTriangular 6 := by
    positivity
  have hone : (1 : ℝ) ≤ growthBar K ^ (IndependentSums.natTriangular 6 + 1) :=
    one_le_pow₀ (by linarith only [hG2])
  have hsucc : growthBar K ^ (IndependentSums.natTriangular 6 + 1) =
      growthBar K ^ IndependentSums.natTriangular 6 * growthBar K := by
    rw [pow_succ]
  rw [sourceMomentSix]
  nlinarith only [hlog, hpow0, hone, hsucc.le, hsucc.ge, hG0, hG2]

end

end HCPolySupport.HighContrast.Quenched
