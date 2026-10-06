/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCoordinateDerivatives

/-!
# Space-time derivatives of the normal cutoff

The factor-wise derivatives of the normal cutoff reduce to its
one-dimensional height and time derivatives.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Only the normal coordinate contributes to the spatial gradient of
the normal cutoff. -/
theorem buShortEtaExt_spatialPartial
    (scale : ℝ) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (buCutScalar (buShortEtaExt scale)) j z =
      deriv (fun y : ℝ => buShortEtaScalar scale y z.2) (z.1 2) *
        (if j = 2 then 1 else 0) := by
  have h := bu_spatialPartial_height
    (fun y : ℝ => buShortEtaScalar scale y z.2) z
    (buShortEtaScalar_height_differentiable scale z.2 (z.1 2)) j
  change (fderiv ℝ (fun x : Vec3 =>
    buShortEtaScalar scale (x 2) z.2) z.1) (basisVec j) = _ at h
  change (fderiv ℝ (fun x : Vec3 =>
    buShortEtaScalar scale (x 2) z.2) z.1) (basisVec j) = _
  exact h

/-- Only the normal coordinate contributes to the diagonal Hessian of
the normal cutoff. -/
theorem buShortEtaExt_spatialSecondPartial_diag
    {scale : ℝ} {z : ParabolicPoint}
    (hy : 2 < z.1 2) (hs : 1 / 2 ≤ z.2)
    (j : Fin 3) :
    spatialSecondPartial (buCutScalar (buShortEtaExt scale)) j j z =
      if j = 2 then
        deriv (fun y : ℝ =>
          deriv (fun r : ℝ => buShortEtaScalar scale r z.2) y) (z.1 2)
      else 0 := by
  have h := bu_spatialSecondPartial_height_diag
    (fun y : ℝ => buShortEtaScalar scale y z.2) z
    (buShortEtaScalar_height_differentiable scale z.2)
    (buShortEtaScalar_height_deriv_differentiable hy hs) j
  calc
    spatialSecondPartial (buCutScalar (buShortEtaExt scale)) j j z =
        spatialSecondPartial
          (fun q : ParabolicPoint =>
            buShortEtaScalar scale (q.1 2) z.2) j j z := by rfl
    _ = _ := h

/-- The time partial derivative of the normal cutoff is its scalar
time derivative. -/
theorem buShortEtaExt_timePartial
    (scale : ℝ) (z : ParabolicPoint) :
    timePartial (buCutScalar (buShortEtaExt scale)) z =
      deriv (fun s : ℝ => buShortEtaScalar scale (z.1 2) s) z.2 := by
  have h := bu_timePartial_time
    (fun s : ℝ => buShortEtaScalar scale (z.1 2) s) z
  change (fderiv ℝ (fun s : ℝ =>
    buShortEtaScalar scale (z.1 2) s) z.2) 1 = _ at h
  change (fderiv ℝ (fun s : ℝ =>
    buShortEtaScalar scale (z.1 2) s) z.2) 1 = _
  exact h

/-- Each spatial derivative of the normal cutoff has linear height
growth on the active strip. -/
theorem buShortEtaExt_spatialPartial_bound
    {scale : ℝ} {z : ParabolicPoint}
    (hscale : 0 < scale) (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1)
    (j : Fin 3) :
    |spatialPartial (buCutScalar (buShortEtaExt scale)) j z| ≤
      (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2) := by
  rw [buShortEtaExt_spatialPartial]
  by_cases hj : j = 2
  · simp only [hj, ite_true, mul_one]
    exact buShortEtaScalar_deriv_height_bound hscale hy hs hs1
  · simp only [hj, ite_false, mul_zero, abs_zero]
    have hK : 0 ≤ 12 / buShortB scale :=
      (div_pos (by norm_num) (buShortB_pos hscale)).le
    positivity

/-- Each diagonal spatial second derivative of the normal cutoff has
quadratic height growth on the active strip. -/
theorem buShortEtaExt_spatialSecondPartial_diag_bound
    {scale C₁ C₂ : ℝ} {z : ParabolicPoint}
    (hscale : 0 < scale) (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (j : Fin 3) :
    |spatialSecondPartial (buCutScalar (buShortEtaExt scale)) j j z| ≤
      (C₁ + 1536 * (12 / buShortB scale) +
        36 * C₂ * (12 / buShortB scale) ^ 2 +
        24 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2 := by
  rw [buShortEtaExt_spatialSecondPartial_diag hy hs]
  by_cases hj : j = 2
  · simp only [hj, ite_true]
    exact buShortEtaScalar_deriv_height_twice_bound
      hscale hy hs hs1 hC₁ hN hC₂ hP
  · simp only [hj, ite_false, abs_zero]
    have hK : 0 ≤ 12 / buShortB scale :=
      (div_pos (by norm_num) (buShortB_pos hscale)).le
    positivity

/-- The time partial derivative of the normal cutoff has quadratic
height growth on the active strip. -/
theorem buShortEtaExt_timePartial_bound
    {scale : ℝ} {z : ParabolicPoint}
    (hscale : 0 < scale) (hy : 2 < z.1 2)
    (hs : 1 / 2 < z.2) (hs1 : z.2 ≤ 1) :
    |timePartial (buCutScalar (buShortEtaExt scale)) z| ≤
      (56 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2 := by
  rw [buShortEtaExt_timePartial]
  exact buShortEtaScalar_deriv_time_bound hscale hy hs hs1

end ESS
