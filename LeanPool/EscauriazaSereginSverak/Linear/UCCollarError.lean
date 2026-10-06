/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCWeightedCarlemanIntegrable

/-!
# Weighted collar error

The heat cutoff error on the spatial and final time collar is controlled
by the unweighted field energy with Gaussian exponential decay.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

/-- The squared collar error is bounded by the full energy multiplied by
the Gaussian collar exponential. -/
theorem uc_gaussian_collar_error_sq_le
    {ρ c₁ scale : ℝ} (hρ : 4 ≤ ρ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    let a := (1 / 100 : ℝ) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
    let A := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
      3 * c₁ * scale * (cutoffGradientConstant / ρ)
    let B := 18 * (cutoffGradientConstant / ρ)
    ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2) ≤
      6 * Real.exp (-(ρ ^ 2) / 100) *
        (A ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
          B ^ 2 * spatialGradientSq v Dv z) := by
  dsimp
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let A : ℝ := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
    3 * c₁ * scale * (cutoffGradientConstant / ρ)
  let B : ℝ := 18 * (cutoffGradientConstant / ρ)
  let E : ℝ := Real.exp (-(ρ ^ 2) / 100)
  let X : ℝ := vec3EuclideanNorm (v z)
  let G : ℝ := spatialGradientSq v Dv z
  let Y : ℝ := Real.sqrt G
  have hG : 0 ≤ G := by dsimp [G, spatialGradientSq]; positivity
  have hY : Y ^ 2 = G := Real.sq_sqrt hG
  have hR : 0 ≤ A ^ 2 * X ^ 2 + B ^ 2 * G := by positivity
  by_cases hz : z ∈ ucCutoffRegion ρ
  · have hw : ucGaussianWeight a z ≤ E :=
      uc_gaussian_collar_weight ρ hρ z hz
    have hsq : 3 * (A * X + B * Y) ^ 2 ≤
        6 * (A ^ 2 * X ^ 2 + B ^ 2 * G) := by
      nlinarith only [sq_nonneg (A * X - B * Y), hY]
    change ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then A * X + B * Y else 0) ^ 2) ≤
      6 * E * (A ^ 2 * X ^ 2 + B ^ 2 * G)
    rw [ite_eq_left hz]
    calc
      ucGaussianWeight a z * (3 * (A * X + B * Y) ^ 2) ≤
          E * (3 * (A * X + B * Y) ^ 2) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ ≤ E * (6 * (A ^ 2 * X ^ 2 + B ^ 2 * G)) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = _ := by ring
  · change ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then A * X + B * Y else 0) ^ 2) ≤
      6 * E * (A ^ 2 * X ^ 2 + B ^ 2 * G)
    rw [ite_eq_right hz]
    simpa using mul_nonneg (by positivity : 0 ≤ 6 * E) hR

/-- The total weighted collar error is bounded by exponentially damped
unweighted field and gradient energy. -/
theorem uc_gaussian_collar_error_integral_le
    {ρ c₁ scale : ℝ} (hρ : 4 ≤ ρ)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let a := (1 / 100 : ℝ) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
    let A := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
      3 * c₁ * scale * (cutoffGradientConstant / ρ)
    let B := 18 * (cutoffGradientConstant / ρ)
    IntegrableOn (fun z => ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2))
      (ucCylinder ρ) volume ∧
    (∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)) ≤
      6 * Real.exp (-(ρ ^ 2) / 100) *
        (∫ z in ucCylinder ρ,
          A ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
            B ^ 2 * spatialGradientSq v Dv z) := by
  dsimp
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let A : ℝ := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
    3 * c₁ * scale * (cutoffGradientConstant / ρ)
  let B : ℝ := 18 * (cutoffGradientConstant / ρ)
  let E : ℝ := Real.exp (-(ρ ^ 2) / 100)
  let μ := volume.restrict (ucCylinder ρ)
  let F : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (3 * (if z ∈ ucCutoffRegion ρ then
      A * vec3EuclideanNorm (v z) +
        B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)
  let G : ParabolicPoint → ℝ := fun z =>
    A ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
      B ^ 2 * spatialGradientSq v Dv z
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hKmeas : MeasurableSet (ucCutoffRegion ρ) := by
    dsimp [ucCutoffRegion, ucCylinder, ucInnerRegion]
    exact ((isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet).diff
      ((isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet)
  obtain ⟨hVInt, hGradInt⟩ := uc_normalized_energy_integrable hweak hL2
  have hGInt : Integrable G μ :=
    (hVInt.const_mul (A ^ 2)).add (hGradInt.const_mul (B ^ 2))
  have hU : Integrable (fun z => 6 * E * G z) μ := hGInt.const_mul (6 * E)
  have hnormMeas : AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (v z)) μ := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hweak.1.aestronglyMeasurable
  have hsqrtMeas : AEStronglyMeasurable
      (fun z => Real.sqrt (spatialGradientSq v Dv z)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      hGradInt.aestronglyMeasurable
  have hI : AEStronglyMeasurable (fun z =>
      if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) μ := by
    have h := ((hnormMeas.const_mul A).add (hsqrtMeas.const_mul B)).indicator hKmeas
    convert h using 1
    funext z
    by_cases hz : z ∈ ucCutoffRegion ρ <;>
      simp [Set.indicator, hz]
  have hFmeas : AEStronglyMeasurable F μ := by
    have h := (ucGaussianWeight_measurable a).aestronglyMeasurable.mul
      ((hI.pow 2).const_mul 3)
    convert h using 1
  have hFnonneg : ∀ᵐ z ∂μ, 0 ≤ F z := by
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    dsimp [F]
    exact mul_nonneg (ucGaussianWeight_nonneg a hz.2.1) (by positivity)
  have hFG : ∀ᵐ z ∂μ, F z ≤ 6 * E * G z := by
    filter_upwards [] with z
    exact uc_gaussian_collar_error_sq_le hρ v Dv z
  have hFInt : Integrable F μ :=
    Integrable.mono_nonneg hU hFmeas hFnonneg hFG
  have hle := integral_mono_ae hFInt hU hFG
  exact ⟨hFInt, by simpa only [integral_const_mul] using hle⟩

end ESS
