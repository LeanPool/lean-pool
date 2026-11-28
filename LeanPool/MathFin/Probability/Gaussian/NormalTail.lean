/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Gaussian.NormalQuantile
public import LeanPool.MathFin.Probability.Gaussian.GaussianPartialMoments
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # The left tail of the standard normal

Four facts about `Φ` and the standard normal density `φ` used to bound option prices far from
the money: `Φ(x) → 0` as `x → −∞`, the Mills bound `−x·Φ(x) ≤ φ(x)`, `φ ≤ 1`, and the
Lipschitz bound on `Φ` that follows.

## Main results

* `tendsto_Phi_atBot`, `tendsto_Phi_atTop`: `Φ(x) → 0` as `x → −∞` and `Φ(x) → 1` as `x → +∞`.
* `neg_mul_Phi_le_gaussianPDFReal`: `−x·Φ(x) ≤ φ(x)` for all `x`.
* `gaussianPDFReal_zero_one_le_one`: the standard normal density is at most `1`.
* `Phi_sub_le`: `Φ` is 1-Lipschitz, `Φ(y) − Φ(x) ≤ y − x` for `x ≤ y`.

## Tags

Mills ratio, normal tail bound, Gaussian tail, deep out-of-the-money option,
standard normal density, MSC 60E15, MSC 91G20
-/

@[expose] public section

namespace MathFin

open Filter Topology ProbabilityTheory MeasureTheory

/-- `Φ` tends to `0` at `−∞`. -/
theorem tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) :=
  cdf_gaussianReal_zero_one ▸ tendsto_cdf_atBot (gaussianReal 0 1)

/-- `Φ` tends to `1` at `+∞`. -/
theorem tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) :=
  cdf_gaussianReal_zero_one ▸ tendsto_cdf_atTop (gaussianReal 0 1)

/-- **The Mills bound**, in the form `−x·Φ(x) ≤ φ(x)`: the stop-loss value
`𝔼[(Z + x)⁺] = φ(x) + x·Φ(x)` of a standard normal `Z` is nonnegative. -/
theorem neg_mul_Phi_le_gaussianPDFReal (x : ℝ) : -x * Phi x ≤ gaussianPDFReal 0 1 x := by
  have h0 : 0 ≤ ∫ y, max (y - -x) 0 * gaussianPDFReal 0 1 y :=
    integral_nonneg fun y ↦ mul_nonneg (le_max_right _ _) (gaussianPDFReal_nonneg _ _ _)
  rw [integral_max_sub_mul_gaussianPDFReal, gaussianPDFReal_zero_one_neg, Phi_neg] at h0
  linarith

/-- The standard normal density is at most `1`. -/
theorem gaussianPDFReal_zero_one_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact (mul_le_of_le_one_left (Real.exp_pos _).le
    (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by nlinarith [Real.pi_gt_three])))).trans
    (Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg x)) zero_le_two))

/-- The standard normal CDF is 1-Lipschitz: `Φ(y) − Φ(x) ≤ y − x` for `x ≤ y` (its density is at
most `1`). -/
theorem Phi_sub_le {x y : ℝ} (hxy : x ≤ y) : Phi y - Phi x ≤ y - x := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Phi) (C := 1) (s := Set.univ)
    (fun z _ ↦ (hasDerivAt_Phi z).differentiableAt)
    (fun z _ ↦ by
      rw [(hasDerivAt_Phi z).deriv, Real.norm_eq_abs,
        abs_of_nonneg (gaussianPDFReal_nonneg 0 1 z)]
      exact gaussianPDFReal_zero_one_le_one z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxy)] at h
  exact (le_abs_self _).trans (by simpa using h)

end MathFin
