/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffGradient

/-!
# Gaussian cutoff operator bound

The normalized heat inequality and the weak product rule separate an
absorbable term from collar and initial time errors.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

/-- The cut off heat operator is controlled by the cut off field and its
weak gradient, with errors confined to the collar and early time. -/
theorem ucGaussianCutoff_operator_ae_bound
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
          (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
        c₁ * scale *
          (vec3EuclideanNorm
            (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
              (ucInitialTimeCutoff ε) v z) +
            3 * Real.sqrt (spatialGradientSq
              (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v)
              (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
                (ucInitialTimeCutoff ε) v Dv) z)) +
        (if z ∈ ucCutoffRegion ρ then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) +
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z) := by
  filter_upwards [ucGaussianCutoff_heat_ae_local_bound hρ hε
    v Dv D2v Dtv hineq] with z hzbound hz
  let ξ := ucGaussianCutoff ρ hρ ε z
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let M := if z ∈ ucCutoffRegion ρ then cutoffGradientConstant / ρ else 0
  have hξ : 0 ≤ ξ := (ucGaussianCutoff_bounds hρ ε z).1
  have hξnorm : ξ * vec3EuclideanNorm (v z) =
      vec3EuclideanNorm (Z z) := by
    change ucGaussianCutoff ρ hρ ε z * vec3EuclideanNorm (v z) = _
    change _ = vec3EuclideanNorm (ξ • v z)
    rw [vec3EuclideanNorm_smul, abs_of_nonneg hξ]
  have hgrad := ucGaussianCutoff_gradient_absorption hρ ε v Dv hz
  change ξ * Real.sqrt (spatialGradientSq v Dv z) ≤
    3 * (Real.sqrt (spatialGradientSq Z DZ z) +
      M * vec3EuclideanNorm (v z)) at hgrad
  have hcoef : 0 ≤ c₁ * scale := mul_nonneg hc₁ hscale
  have hmain : ξ * (c₁ * scale *
      (vec3EuclideanNorm (v z) +
        Real.sqrt (spatialGradientSq v Dv z))) ≤
      c₁ * scale * (vec3EuclideanNorm (Z z) +
        3 * Real.sqrt (spatialGradientSq Z DZ z)) +
      3 * c₁ * scale * M * vec3EuclideanNorm (v z) := by
    calc
      ξ * (c₁ * scale *
          (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) =
        c₁ * scale * (ξ * vec3EuclideanNorm (v z) +
          ξ * Real.sqrt (spatialGradientSq v Dv z)) := by ring
      _ ≤ c₁ * scale * (vec3EuclideanNorm (Z z) +
          3 * (Real.sqrt (spatialGradientSq Z DZ z) +
            M * vec3EuclideanNorm (v z))) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        rw [hξnorm]
        exact add_le_add le_rfl hgrad
      _ = _ := by ring
  have h := hzbound hz
  change vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      ξ * (c₁ * scale *
        (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) +
      (if z ∈ ucCutoffRegion ρ then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) at h
  have hsum : vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
      (c₁ * scale * (vec3EuclideanNorm (Z z) +
        3 * Real.sqrt (spatialGradientSq Z DZ z)) +
        3 * c₁ * scale * M * vec3EuclideanNorm (v z)) +
      (if z ∈ ucCutoffRegion ρ then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
    exact h.trans (add_le_add (add_le_add hmain le_rfl) le_rfl)
  by_cases hc : z ∈ ucCutoffRegion ρ
  · convert hsum using 1
    simp only [M, hc, ↓reduceIte]
    ring
  · convert hsum using 1
    simp only [M, hc, ↓reduceIte]
    ring

end ESS
