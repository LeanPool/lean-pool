/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Derivative of the inverse of an operator-valued function

For `H : E → R` into a complete normed algebra with `H x` a unit, `y ↦ Ring.inverse (H y)` is
differentiable at `x` with derivative `v ↦ −H(x)⁻¹ (DH(x)[v]) H(x)⁻¹` (noncommutative order kept).
Used for the derivative of the inverse Hessian (Letwin (2.5)).
-/

@[expose] public section

noncomputable section
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

/--
Derivative of `y ↦ Ring.inverse (H y)` at a point where `H y` is a unit (composition with Mathlib's
`hasFDerivAt_ringInverse`). -/
theorem hasFDerivAt_ringInverse_comp {H : E → R} {H' : E →L[ℝ] R} {x : E}
    (hH : HasFDerivAt H H' x) (hunit : IsUnit (H x)) :
    HasFDerivAt (fun y => Ring.inverse (H y))
      (-ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse (H x)) (Ring.inverse (H x)) ∘L H')
      x := by
  obtain ⟨a, ha⟩ := hunit
  have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) a
  have hInv : (↑a⁻¹ : R) = Ring.inverse (H x) := by rw [← ha, Ring.inverse_unit]
  rw [ha, hInv] at hd
  exact hd.comp x hH

/-- `D(H⁻¹)(x)[v] = −H(x)⁻¹ (DH(x)[v]) H(x)⁻¹`. -/
theorem fderiv_ringInverse_comp_apply {H : E → R} {x : E}
    (hH : DifferentiableAt ℝ H x) (hunit : IsUnit (H x)) (v : E) :
    fderiv ℝ (fun y => Ring.inverse (H y)) x v =
      -(Ring.inverse (H x) * fderiv ℝ H x v * Ring.inverse (H x)) := by
  rw [(hasFDerivAt_ringInverse_comp hH.hasFDerivAt hunit).fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.mulLeftRight_apply]

end FunctionalInequalities.Analysis
