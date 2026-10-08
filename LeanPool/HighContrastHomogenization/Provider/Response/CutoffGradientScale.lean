/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffDerivatives

/-!
# High-contrast homogenization: Provider.Response.CutoffGradientScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gradient scale of the adapted cutoff

The adapted cutoff is the canonical smooth product cutoff between two
concentric reference cubes of relative radii `1 - 1/(2d)` and `1 - 1/(4d)`,
normalized to have reference mean one and pulled forward by the grid matrix.

Two quantitative facts about that construction are recorded here.

* Its normalizing average is at most one, because the unnormalized product
  cutoff is bounded by one.  Consequently the normalized cutoff takes a value
  at least one on the inner cube and vanishes off the outer cube, and a
  one-dimensional mean value argument along a coordinate segment produces a
  point at which the adapted-coordinate gradient is at least the reciprocal
  collar width `8d·3^{-t}`.  Since `4(d+1) < 8d` whenever `d ≥ 2`, no bound of
  the form `‖q∇φ‖ ≤ 4(d+1)·3^{-t}` can hold for this cutoff.
* In the opposite direction the same construction obeys the sharper first
  derivative bound with coefficient `32 d² θ'`, where `θ'` is the derivative
  bound of the one-dimensional transition profile.  This is the smallest
  coefficient the construction supports; the coefficient recorded downstream is
  the common second-order enlargement of it.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Set MeasureTheory

variable {d : ℕ}

/-- The smallest first-derivative coefficient the adapted construction
supports:  the reference gradient bound of the transition profile, doubled by
normalization and multiplied by the reciprocal collar width. -/
theorem adaptedPreYoungCutoff_pullback_fderiv_bound_sharp [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (x : Vec d) :
    ‖fderiv ℝ (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) x‖ ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound * (3 : ℝ) ^ (-t) := by
  obtain ⟨hρ₁, hρ₁₂, _hρ₂⟩ := cutoffRadii_spec d
  set eta : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun (originCube d t)
    (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ))) with heta
  set A : ℝ := cubeAverage (originCube d t) eta with hA
  have hApos : 0 < A := by
    rw [hA, heta]
    exact adaptedPreYoungCutoff_rawAverage_pos (d := d) t
  have hAinv : 0 ≤ A⁻¹ := inv_nonneg.mpr hApos.le
  have hAinv_le : A⁻¹ ≤ 2 := by
    rw [hA, heta]
    exact adaptedPreYoungCutoff_inv_rawAverage_le_two (d := d) t
  have hpull : (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) =
      fun y => A⁻¹ * eta y := by
    funext y
    simpa [hA, heta] using adaptedPreYoungCutoff_pullback_apply hq t y
  have hraw := QuantitativeCubeCutoff.canonicalFun_gradient_bound
    (originCube d t) hρ₁ hρ₁₂ x
  rw [adaptedPreYoungCutoff_transitionScale (d := d) t] at hraw
  have hnorm : ‖fderiv ℝ (fun y => A⁻¹ * eta y) x‖ = A⁻¹ * ‖fderiv ℝ eta x‖ := by
    rw [show (fun y => A⁻¹ * eta y) = A⁻¹ • eta by
      funext y
      exact (smul_eq_mul _ _).symm]
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hAinv]
  rw [hpull, hnorm]
  calc
    A⁻¹ * ‖fderiv ℝ eta x‖ ≤
        2 * ((d : ℝ) * smoothTransitionProfile.derivBound *
          (16 * (d : ℝ) * (3 : ℝ) ^ (-t))) :=
      mul_le_mul hAinv_le hraw (norm_nonneg _) (by positivity)
    _ = 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-t) := by ring

end

end Response
end HighContrast
end HCPolySupport
