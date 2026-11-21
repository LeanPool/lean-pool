/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanWeakHessianEstimates

/-! # Actual mollification of distributional first derivatives

Actual compact smooth test identities imply an everywhere identity between
the actual classical derivative of a smoothing and the smoothing of its
actual weak derivative. No pointwise differentiability of the input occurs.
-/

public section

namespace CutoffRigidity

open MeasureTheory ContinuousLinearMap
open scoped Convolution

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Weak first derivatives commute with actual compact smooth convolution. -/
theorem coordinateDerivative_convolution_of_weak_derivative
    {g H k : E → ℝ} (hg : LocallyIntegrable g volume)
    (hk : ContDiff ℝ 3 k) (hkc : HasCompactSupport k) (j : Fin d)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H y * ψ y)) (x : E) :
    coordinateDerivative j (k ⋆[lsmul ℝ ℝ, volume] g) x = (k ⋆[lsmul ℝ ℝ, volume] H) x := by
  rw [coordinateDerivative_convolution_kernel (hk.of_le (by norm_num)) hkc hg,
    scalar_convolution_eq_shifted_kernel, scalar_convolution_eq_shifted_kernel]
  let ψ (y : E) := k (x - y)
  have hψ : ContDiff ℝ 3 ψ := hk.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := hweak ψ hψ hψc
  have hp (y : E) : coordinateDerivative j ψ y = -coordinateDerivative j k (x - y) :=
    coordinateDerivative_reflect (hk.differentiable (by norm_num)) x j y
  simp_rw [hp] at hh
  simp only [mul_neg, integral_neg] at hh
  have he := neg_inj.mp hh
  simpa only [ψ, mul_comm] using he

/-- The normalized Mathlib bump specialization, for use in actual weak-H¹
approximation and closed-gradient graph construction. -/
theorem coordinateDerivative_bumpMollification_of_weak_derivative
    (φ : ContDiffBump (0 : E)) {g H : E → ℝ}
    (hg : LocallyIntegrable g volume) (j : Fin d)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H y * ψ y)) (x : E) :
    coordinateDerivative j (bumpMollification φ g) x = bumpMollification φ H x :=
  coordinateDerivative_convolution_of_weak_derivative hg (φ.contDiff_normed (n := 3))
    φ.hasCompactSupport_normed j hweak x

end CutoffRigidity
