/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffOperatorBound

/-!
# Squared Gaussian cutoff operator bound

The pointwise weak heat inequality has a quadratic form suited to the
Gaussian Carleman integral.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

private theorem uc_sq_three_le_three (u v w : ℝ) :
    (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
  nlinarith only [sq_nonneg (u - v), sq_nonneg (u - w),
    sq_nonneg (v - w)]

/-- The squared weak heat operator separates an absorbable cutoff energy
from quadratic collar and initial time errors. -/
theorem ucGaussianCutoff_operator_sq_ae_bound
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      z ∈ ucCylinder ρ →
      vec3EuclideanNorm
        (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ^ 2 ≤
        54 * (c₁ * scale) ^ 2 *
          (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) ^ 2 +
            spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z) +
        3 * (if z ∈ ucCutoffRegion ρ then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2 +
        3 * ((if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z)) ^ 2 := by
  filter_upwards [ucGaussianCutoff_operator_ae_bound hρ hε hc₁ hscale
    v Dv D2v Dtv hineq] with z hzbound hz
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv z
  let x := vec3EuclideanNorm (Z z)
  let y := Real.sqrt (spatialGradientSq Z DZ z)
  let q := c₁ * scale
  let A := q * (x + 3 * y)
  let B := if z ∈ ucCutoffRegion ρ then
    (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
      3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
        vec3EuclideanNorm (v z) +
    18 * (cutoffGradientConstant / ρ) *
      Real.sqrt (spatialGradientSq v Dv z) else 0
  let C := (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
    vec3EuclideanNorm (v z)
  have hL : vec3EuclideanNorm LZ ≤ A + B + C := hzbound hz
  have hL0 : 0 ≤ vec3EuclideanNorm LZ := vec3EuclideanNorm_nonneg _
  have hsq : vec3EuclideanNorm LZ ^ 2 ≤ (A + B + C) ^ 2 :=
    (sq_le_sq₀ hL0 (hL0.trans hL)).2 hL
  have hG : 0 ≤ spatialGradientSq Z DZ z := by
    dsimp [spatialGradientSq]
    positivity
  have hy : y ^ 2 = spatialGradientSq Z DZ z :=
    Real.sq_sqrt hG
  have hsum : (x + 3 * y) ^ 2 ≤
      18 * (x ^ 2 + spatialGradientSq Z DZ z) := by
    dsimp [x] at *
    nlinarith only [sq_nonneg (x - 3 * y), sq_nonneg x, hy]
  have hA : A ^ 2 ≤
      18 * q ^ 2 * (x ^ 2 + spatialGradientSq Z DZ z) := by
    calc
      A ^ 2 = q ^ 2 * (x + 3 * y) ^ 2 := by dsimp [A]; ring
      _ ≤ q ^ 2 * (18 * (x ^ 2 + spatialGradientSq Z DZ z)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg q)
      _ = _ := by ring
  change vec3EuclideanNorm LZ ^ 2 ≤
    54 * q ^ 2 * (x ^ 2 + spatialGradientSq Z DZ z) +
      3 * B ^ 2 + 3 * C ^ 2
  calc
    vec3EuclideanNorm LZ ^ 2 ≤ (A + B + C) ^ 2 := hsq
    _ ≤ 3 * (A ^ 2 + B ^ 2 + C ^ 2) :=
      uc_sq_three_le_three A B C
    _ ≤ 54 * q ^ 2 * (x ^ 2 + spatialGradientSq Z DZ z) +
        3 * B ^ 2 + 3 * C ^ 2 := by
      nlinarith only [hA]

end ESS
