/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSpacePhaseDerivatives

/-!
# Bounds for the spatial and normal cutoff product

The spatial shell terms carry inverse powers of the radius, while the
normal-phase terms have fixed polynomial height growth.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The first spatial derivative of the two-factor cutoff separates
the shell and normal-phase contributions. -/
theorem buShortSpacePhase_spatialPartial_bound
    {scale R : ℝ} (hscale : 0 < scale) (hR : 0 < R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1)
    (j : Fin 3) :
    |spatialPartial
      (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j z| ≤
      cutoffGradientConstant / (2 * R) +
        (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2) := by
  let Cχ := cutoffGradientConstant / (2 * R)
  let Cη := (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)
  have hχ := ucSpatialCutoff_spatialPartial_bound
    (show 0 < 2 * R by positivity) z j
  have hη := buShortEtaExt_spatialPartial_bound hscale hy hs hs1 j
  have hχval := ucSpatialCutoff_bounds
    (show 0 < 2 * R by positivity) z.1
  have hηval := buShortEtaExt_bounds scale (z.1, z.2)
  rw [buShortSpacePhase_spatialPartial scale R hR j z]
  have hfirst :
      |spatialPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
        buShortEtaExt scale (z.1, z.2)| ≤ Cχ := by
    rw [abs_mul, abs_of_nonneg hηval.1]
    calc
      _ ≤ Cχ * 1 := by
        exact mul_le_mul hχ hηval.2 hηval.1
          ((abs_nonneg _).trans hχ)
      _ = Cχ := by ring
  have hsecond :
      |ucSpatialCutoff (2 * R) (by positivity) z.1 *
        spatialPartial (buCutScalar (buShortEtaExt scale)) j z| ≤ Cη := by
    rw [abs_mul, abs_of_nonneg hχval.1]
    calc
      _ ≤ 1 * Cη := by
        exact mul_le_mul hχval.2 hη (abs_nonneg _) (by norm_num)
      _ = Cη := by ring
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The diagonal spatial second derivative separates its shell,
mixed, and normal-phase contributions. -/
theorem buShortSpacePhase_spatialSecondPartial_diag_bound
    {scale R C₁ C₂ : ℝ} (hscale : 0 < scale) (hR : 0 < R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 ≤ z.2) (hs1 : z.2 ≤ 1)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (j : Fin 3) :
    |spatialSecondPartial
      (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j j z| ≤
      cutoffSecondDerivativeConstant / (2 * R) ^ 2 +
      2 * (cutoffGradientConstant / (2 * R)) *
        ((16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)) +
      (C₁ + 1536 * (12 / buShortB scale) +
        36 * C₂ * (12 / buShortB scale) ^ 2 +
        24 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2 := by
  let Cχ := cutoffGradientConstant / (2 * R)
  let Cχ₂ := cutoffSecondDerivativeConstant / (2 * R) ^ 2
  let Cη := (16 + 48 * (12 / buShortB scale)) * (1 + z.1 2)
  let Cη₂ := (C₁ + 1536 * (12 / buShortB scale) +
    36 * C₂ * (12 / buShortB scale) ^ 2 +
    24 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2
  have hχ := ucSpatialCutoff_spatialPartial_bound
    (show 0 < 2 * R by positivity) z j
  have hχ₂ := ucSpatialCutoff_spatialSecondPartial_bound
    (show 0 < 2 * R by positivity) z j j
  have hη := buShortEtaExt_spatialPartial_bound hscale hy hs hs1 j
  have hη₂ := buShortEtaExt_spatialSecondPartial_diag_bound
    hscale hy hs hs1 hC₁ hN hC₂ hP j
  have hχval := ucSpatialCutoff_bounds
    (show 0 < 2 * R by positivity) z.1
  have hηval := buShortEtaExt_bounds scale (z.1, z.2)
  have hCχ : 0 ≤ Cχ := (abs_nonneg _).trans hχ
  have hCχ₂ : 0 ≤ Cχ₂ := (abs_nonneg _).trans hχ₂
  have hCη : 0 ≤ Cη := (abs_nonneg _).trans hη
  have hCη₂ : 0 ≤ Cη₂ := (abs_nonneg _).trans hη₂
  rw [buShortSpacePhase_spatialSecondPartial_diag scale R hR j z]
  have hfirst :
      |spatialSecondPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j j z *
        buShortEtaExt scale (z.1, z.2)| ≤ Cχ₂ := by
    rw [abs_mul, abs_of_nonneg hηval.1]
    calc
      _ ≤ Cχ₂ * 1 := by
        exact mul_le_mul hχ₂ hηval.2 hηval.1 hCχ₂
      _ = Cχ₂ := by ring
  have hcross :
      |2 * spatialPartial
          (fun q : ParabolicPoint =>
            ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
        spatialPartial (buCutScalar (buShortEtaExt scale)) j z| ≤
        2 * Cχ * Cη := by
    rw [abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  have hlast :
      |ucSpatialCutoff (2 * R) (by positivity) z.1 *
        spatialSecondPartial
          (buCutScalar (buShortEtaExt scale)) j j z| ≤ Cη₂ := by
    rw [abs_mul, abs_of_nonneg hχval.1]
    calc
      _ ≤ 1 * Cη₂ := by
        exact mul_le_mul hχval.2 hη₂ (abs_nonneg _) (by norm_num)
      _ = Cη₂ := by ring
  have htri := abs_add_le
    (spatialSecondPartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) j j z *
        buShortEtaExt scale (z.1, z.2) +
      2 * spatialPartial
        (fun q : ParabolicPoint =>
          ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
        spatialPartial (buCutScalar (buShortEtaExt scale)) j z)
    (ucSpatialCutoff (2 * R) (by positivity) z.1 *
      spatialSecondPartial
        (buCutScalar (buShortEtaExt scale)) j j z)
  have htri₂ := abs_add_le
    (spatialSecondPartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) j j z *
      buShortEtaExt scale (z.1, z.2))
    (2 * spatialPartial
      (fun q : ParabolicPoint =>
        ucSpatialCutoff (2 * R) (by positivity) q.1) j z *
      spatialPartial (buCutScalar (buShortEtaExt scale)) j z)
  linarith only [htri, htri₂, hfirst, hcross, hlast]

/-- The time derivative of the two-factor cutoff has only the
normal-phase contribution. -/
theorem buShortSpacePhase_timePartial_bound
    {scale R : ℝ} (hscale : 0 < scale) (hR : 0 < R)
    {z : ParabolicPoint} (hy : 2 < z.1 2)
    (hs : 1 / 2 < z.2) (hs1 : z.2 ≤ 1) :
    |timePartial
      (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z| ≤
      (56 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2 := by
  rw [buShortSpacePhase_timePartial scale R hR z, abs_mul]
  have hχ := ucSpatialCutoff_bounds
    (show 0 < 2 * R by positivity) z.1
  rw [abs_of_nonneg hχ.1]
  calc
    _ ≤ 1 * ((56 * (12 / buShortB scale)) * (1 + z.1 2) ^ 2) := by
      exact mul_le_mul hχ.2
        (buShortEtaExt_timePartial_bound hscale hy hs hs1)
        (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end ESS
