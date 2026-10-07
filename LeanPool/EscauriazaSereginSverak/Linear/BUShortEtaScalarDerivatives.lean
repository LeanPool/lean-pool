/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseFactorBounds

/-!
# Derivatives of the normal cutoff

The two-variable scalar cutoff is a product of a fixed-width height
transition and the smooth normal-phase transition.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The scalar form of the extended normal cutoff. -/
@[expose] def buShortEtaScalar (scale y s : ℝ) : ℝ :=
  buShortNormalCutoff scale y * buShortPhaseFactor scale y s

private theorem buShortNormalCutoff_differentiable (scale : ℝ) :
    Differentiable ℝ (buShortNormalCutoff scale) := by
  rw [buShortNormalCutoff_affine]
  have harg : Differentiable ℝ
      (fun y : ℝ => 2 * (y - buShortYMinus scale)) := by fun_prop
  exact (smoothTransitionProfile.smooth.differentiable (by simp)).comp harg

private theorem buShortPhaseFactor_height_differentiable
    (scale s : ℝ) :
    Differentiable ℝ (fun y => buShortPhaseFactor scale y s) := by
  have hF : Differentiable ℝ (fun r : ℝ => buShortFExt r s) := by
    have hpair : ContDiff ℝ (⊤ : ℕ∞)
        (fun r : ℝ => ((r, s) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
  have harg : Differentiable ℝ
      (fun y : ℝ => buShortPhaseArgument scale y s) := by
    unfold buShortPhaseArgument
    fun_prop
  exact (smoothTransitionProfile.smooth.differentiable (by simp)).comp harg

private theorem buShortPhaseFactor_time_differentiable
    (scale y : ℝ) :
    Differentiable ℝ (fun s => buShortPhaseFactor scale y s) := by
  have hF : Differentiable ℝ (fun t : ℝ => buShortFExt y t) := by
    have hpair : ContDiff ℝ (⊤ : ℕ∞)
        (fun t : ℝ => ((y, t) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
  have harg : Differentiable ℝ
      (fun s : ℝ => buShortPhaseArgument scale y s) := by
    unfold buShortPhaseArgument
    fun_prop
  exact (smoothTransitionProfile.smooth.differentiable (by simp)).comp harg

private theorem buShortNormalCutoff_deriv_differentiable (scale : ℝ) :
    Differentiable ℝ (deriv (buShortNormalCutoff scale)) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => 2 * (y - buShortYMinus scale)) := by fun_prop
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (buShortNormalCutoff scale) := by
    rw [buShortNormalCutoff_affine]
    exact smoothTransitionProfile.smooth.comp harg
  have h := hcut.differentiable_iteratedDeriv 1 (by simp)
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

private theorem buShortPhaseFactor_height_deriv_differentiable
    {scale y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    DifferentiableAt ℝ
      (fun r : ℝ => deriv (fun q : ℝ =>
        buShortPhaseFactor scale q s) r) y := by
  have hfun :
      (fun r : ℝ => deriv (fun q : ℝ =>
        buShortPhaseFactor scale q s) r) =
      (fun r => deriv smoothTransitionProfile
        (buShortPhaseArgument scale r s) *
          (12 / buShortB scale *
            deriv (fun q : ℝ => buShortFExt q s) r)) := by
    funext r
    exact buShortPhaseFactor_deriv_height scale r s
  rw [hfun]
  have hF : Differentiable ℝ (fun r : ℝ => buShortFExt r s) := by
    have hpair : ContDiff ℝ (⊤ : ℕ∞)
        (fun r : ℝ => ((r, s) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    exact (buShortFExt_smooth.comp hpair).differentiable (by simp)
  have harg : DifferentiableAt ℝ
      (fun r : ℝ => buShortPhaseArgument scale r s) y := by
    unfold buShortPhaseArgument
    fun_prop
  have hprofile : Differentiable ℝ (deriv smoothTransitionProfile) := by
    have h := smoothTransitionProfile.smooth.differentiable_iteratedDeriv 1
      (by simp)
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  exact ((hprofile _).comp y harg).mul
    ((buShortFExt_height_deriv_differentiable hy hs).const_mul _)

/-- The normal cutoff is differentiable in height at every point. -/
theorem buShortEtaScalar_height_differentiable
    (scale s : ℝ) :
    Differentiable ℝ (fun y : ℝ => buShortEtaScalar scale y s) := by
  exact (buShortNormalCutoff_differentiable scale).mul
    (buShortPhaseFactor_height_differentiable scale s)

/-- The first height derivative obeys the product rule. -/
theorem buShortEtaScalar_deriv_height (scale y s : ℝ) :
    deriv (fun r : ℝ => buShortEtaScalar scale r s) y =
      deriv (buShortNormalCutoff scale) y *
        buShortPhaseFactor scale y s +
      buShortNormalCutoff scale y *
        deriv (fun r : ℝ => buShortPhaseFactor scale r s) y := by
  have hprod := (buShortNormalCutoff_differentiable scale y).hasDerivAt.mul
    (buShortPhaseFactor_height_differentiable scale s y).hasDerivAt
  change deriv (fun r : ℝ =>
    buShortNormalCutoff scale r * buShortPhaseFactor scale r s) y = _
  change HasDerivAt (fun r : ℝ =>
    buShortNormalCutoff scale r * buShortPhaseFactor scale r s) _ y at hprod
  exact hprod.deriv

/-- The first height derivative of the normal cutoff is differentiable
on the active strip. -/
theorem buShortEtaScalar_height_deriv_differentiable
    {scale y s : ℝ} (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    DifferentiableAt ℝ
      (fun r : ℝ => deriv (fun q : ℝ =>
        buShortEtaScalar scale q s) r) y := by
  have hfun :
      (fun r : ℝ => deriv (fun q : ℝ =>
        buShortEtaScalar scale q s) r) =
      (fun r => deriv (buShortNormalCutoff scale) r *
        buShortPhaseFactor scale r s +
        buShortNormalCutoff scale r *
          deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) := by
    funext r
    exact buShortEtaScalar_deriv_height scale r s
  rw [hfun]
  exact ((buShortNormalCutoff_deriv_differentiable scale y).mul
    (buShortPhaseFactor_height_differentiable scale s y)).add
    ((buShortNormalCutoff_differentiable scale y).mul
      (buShortPhaseFactor_height_deriv_differentiable
        (scale := scale) hy hs))

/-- The time derivative acts only on the phase transition factor. -/
theorem buShortEtaScalar_deriv_time (scale y s : ℝ) :
    deriv (fun t : ℝ => buShortEtaScalar scale y t) s =
      buShortNormalCutoff scale y *
        deriv (fun t : ℝ => buShortPhaseFactor scale y t) s := by
  have hprod :=
    (buShortPhaseFactor_time_differentiable scale y s).hasDerivAt.const_mul
      (buShortNormalCutoff scale y)
  change deriv (fun t : ℝ =>
    buShortNormalCutoff scale y * buShortPhaseFactor scale y t) s = _
  exact hprod.deriv

/-- The second height derivative obeys the iterated product rule. -/
theorem buShortEtaScalar_deriv_height_twice
    (scale y s : ℝ) (hy : 2 < y) (hs : 1 / 2 ≤ s) :
    deriv (fun r : ℝ =>
      deriv (fun q : ℝ => buShortEtaScalar scale q s) r) y =
      deriv (deriv (buShortNormalCutoff scale)) y *
        buShortPhaseFactor scale y s +
      2 * deriv (buShortNormalCutoff scale) y *
        deriv (fun r : ℝ => buShortPhaseFactor scale r s) y +
      buShortNormalCutoff scale y *
        deriv (fun r : ℝ =>
          deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) y := by
  have hfun :
      (fun r : ℝ =>
        deriv (fun q : ℝ => buShortEtaScalar scale q s) r) =
      (fun r => deriv (buShortNormalCutoff scale) r *
        buShortPhaseFactor scale r s +
        buShortNormalCutoff scale r *
          deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) := by
    funext r
    exact buShortEtaScalar_deriv_height scale r s
  rw [hfun]
  have hfirst :=
    (buShortNormalCutoff_deriv_differentiable scale y).hasDerivAt.mul
      (buShortPhaseFactor_height_differentiable scale s y).hasDerivAt
  have hsecond :=
    (buShortNormalCutoff_differentiable scale y).hasDerivAt.mul
      (buShortPhaseFactor_height_deriv_differentiable
        (scale := scale) hy hs).hasDerivAt
  have hsum := hfirst.add hsecond
  change HasDerivAt
    (fun r => deriv (buShortNormalCutoff scale) r *
      buShortPhaseFactor scale r s +
      buShortNormalCutoff scale r *
        deriv (fun q : ℝ => buShortPhaseFactor scale q s) r) _ y at hsum
  convert hsum.deriv using 1
  ring

end ESS
