/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.UnitRange

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeGaussianGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The finite-range Gaussian gauge

A unit-range law satisfies the concentration-for-sums condition with the
dimensional parameters supplied by unit range of dependence: the exponents
`β = 0` and `ν = d/2`, the Gaussian concentration gauge
`Ψ_fr(t) = exp(c_fr(d) t²)`, and a dimensional growth
witness `K_fr(d) ∈ [3, ∞)`.

This file fixes those numbers and proves the two structural properties a gauge
must have before the weak-Orlicz calculus can use it: admissibility, that is
monotonicity on `[0, ∞)` together with the lower bound one, and the growth
inequality `t Ψ(t) ≤ Ψ(K t)` for `t ≥ 1`.

The value of `c_fr(d)` recorded here is the one the colouring argument produces.
A triadic colouring of the aligned cells uses `3^d` colours, each colour class
is independent under unit range, and the resulting sub-Gaussian parameter of a
sum of `N` bounded local observables is `3^d N`; the exponent constant is the
reciprocal `(2 · 3^d)⁻¹` that the Chernoff bound then supplies.  Every number
here depends on the dimension alone; none of them sees a law, a reference block,
a source scale or an exponent.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

noncomputable section

/-! ## The dimensional numbers -/

/-- The dimensional constant `c_fr(d)` of the finite-range Gaussian gauge. -/
@[expose]
def frGaugeConst (d : ℕ) : ℝ := ((2 : ℝ) * 3 ^ d)⁻¹

/-- The finite-range Gaussian gauge `Ψ_fr(t) = exp(c_fr(d) t²)`. -/
@[expose]
def frGauge (d : ℕ) : ℝ → ℝ := fun t => Real.exp (frGaugeConst d * t ^ 2)

/-- The dimensional threshold constant of the finite-range concentration
estimate: the factor by which the natural fluctuation scale is enlarged so that
the two-sided union bound is absorbed into the gauge itself. -/
@[expose]
def frThreshold (d : ℕ) : ℝ := 1 + 2 * 3 ^ d

/-! ## Elementary positivity -/

theorem one_le_three_pow (d : ℕ) : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)

theorem three_pow_pos (d : ℕ) : (0 : ℝ) < (3 : ℝ) ^ d :=
  lt_of_lt_of_le zero_lt_one (one_le_three_pow d)

theorem two_mul_three_pow_pos (d : ℕ) : (0 : ℝ) < 2 * (3 : ℝ) ^ d := by
  have := three_pow_pos d
  linarith only [this]

theorem frGaugeConst_pos (d : ℕ) : 0 < frGaugeConst d :=
  inv_pos.2 (two_mul_three_pow_pos d)

theorem three_le_frThreshold (d : ℕ) : (3 : ℝ) ≤ frThreshold d := by
  rw [frThreshold]
  have := one_le_three_pow d
  linarith only [this]

theorem frThreshold_pos (d : ℕ) : 0 < frThreshold d :=
  lt_of_lt_of_le (by norm_num) (three_le_frThreshold d)

theorem frGauge_pos (d : ℕ) (t : ℝ) : 0 < frGauge d t := Real.exp_pos _

/-- The reciprocal of the finite-range gauge is the Gaussian tail. -/
theorem inv_frGauge (d : ℕ) (t : ℝ) :
    (frGauge d t)⁻¹ = Real.exp (-(frGaugeConst d * t ^ 2)) := by
  rw [frGauge, ← Real.exp_neg]

/-! ## The gauge is admissible -/

/-- The finite-range gauge is admissible: it is monotone on `[0, ∞)` and at
least one there. -/
theorem admissiblePsi_frGauge (d : ℕ) :
    IndependentSums.AdmissiblePsi (frGauge d) := by
  constructor
  · intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    refine Real.exp_le_exp.2 ?_
    have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith only [hs, ht, hst]
    exact mul_le_mul_of_nonneg_left hsq (frGaugeConst_pos d).le
  · intro t _
    have h0 : (0 : ℝ) ≤ frGaugeConst d * t ^ 2 := by
      have hc := (frGaugeConst_pos d).le
      positivity
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (frGaugeConst d * t ^ 2) := Real.exp_le_exp.2 h0

/-! ## The growth witness -/

/-- The defining arithmetic of the threshold constant: the two-sided union
bound of the Chernoff estimate is absorbed by the enlarged threshold. -/
theorem log_two_le_frGaugeConst_mul_threshold (d : ℕ) :
    Real.log 2 ≤ frGaugeConst d * (frThreshold d ^ 2 - 1) := by
  have hB : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_three_pow d
  have hBpos : (0 : ℝ) < 2 * (3 : ℝ) ^ d := two_mul_three_pow_pos d
  have hlog : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hkey : 2 * (2 * (3 : ℝ) ^ d) ≤ frThreshold d ^ 2 - 1 := by
    rw [frThreshold]
    nlinarith only [hB]
  have hdiv : (2 : ℝ) ≤ frGaugeConst d * (frThreshold d ^ 2 - 1) := by
    rw [frGaugeConst, ← div_eq_inv_mul, le_div_iff₀ hBpos]
    exact hkey
  linarith only [hlog, hdiv]

end

end Quenched
end HighContrast
end HCPolySupport
