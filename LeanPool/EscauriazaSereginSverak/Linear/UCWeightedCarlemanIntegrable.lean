/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCWeightedCutoffOperator

/-!
# Integrable Gaussian cutoff terms

The Carleman field, gradient, and heat terms are integrable in product
coordinates for every positive initial cutoff time.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The field and gradient parts of the weighted cutoff energy are
individually integrable. -/
theorem uc_weighted_cutoff_components_integrable
    {ρ ε a : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    IntegrableOn (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm (Z z) ^ 2) (ucCylinder ρ) volume ∧
    IntegrableOn (fun z => ucGaussianWeight a z *
      spatialGradientSq Z DZ z) (ucCylinder ρ) volume) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let D2Z := ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v
  let DtZ := ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dtv
  obtain ⟨hweakZ, _, _, hL2Z⟩ :=
    ucGaussianCutoff_admissible hρ hε hweak hL2
  change HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
    Z DZ D2Z DtZ at hweakZ
  change (∫⁻ z in ucCylinder ρ,
      ‖Z z‖ₑ ^ (2 : ℝ) + ‖DZ z‖ₑ ^ (2 : ℝ) +
        ‖D2Z z‖ₑ ^ (2 : ℝ) + ‖DtZ z‖ₑ ^ (2 : ℝ)) < ⊤ at hL2Z
  obtain ⟨hZInt, hDZInt⟩ := uc_normalized_energy_integrable hweakZ hL2Z
  have hSumInt := uc_weighted_cutoff_energy_integrable hρ hε ha hweak hL2
  change IntegrableOn (fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z))
    (ucCylinder ρ) volume at hSumInt
  have hZmeas : AEStronglyMeasurable (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm (Z z) ^ 2)
      (volume.restrict (ucCylinder ρ)) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mul
      hZInt.aestronglyMeasurable
  have hDZmeas : AEStronglyMeasurable (fun z => ucGaussianWeight a z *
      spatialGradientSq Z DZ z)
      (volume.restrict (ucCylinder ρ)) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mul
      hDZInt.aestronglyMeasurable
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  constructor
  · apply Integrable.mono_nonneg hSumInt hZmeas
    · filter_upwards [ae_restrict_mem hQmeas] with z hz
      exact mul_nonneg (ucGaussianWeight_nonneg a hz.2.1) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem hQmeas] with z hz
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by dsimp [spatialGradientSq]; positivity))
        (ucGaussianWeight_nonneg a hz.2.1)
  · apply Integrable.mono_nonneg hSumInt hDZmeas
    · filter_upwards [ae_restrict_mem hQmeas] with z hz
      exact mul_nonneg (ucGaussianWeight_nonneg a hz.2.1)
        (by dsimp [spatialGradientSq]; positivity)
    · filter_upwards [ae_restrict_mem hQmeas] with z hz
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (sq_nonneg _))
        (ucGaussianWeight_nonneg a hz.2.1)

/-- The positive-time cutoff makes the Carleman mass term integrable,
including its inverse time factor. -/
theorem uc_weighted_cutoff_mass_over_time_integrable
    {ρ ε a : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    IntegrableOn (fun z => ucGaussianWeight a z * (a / z.2) *
      vec3EuclideanNorm (Z z) ^ 2) (ucCylinder ρ) volume) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let μ := volume.restrict (ucCylinder ρ)
  let W : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * vec3EuclideanNorm (Z z) ^ 2
  have hW : Integrable W μ :=
    (uc_weighted_cutoff_components_integrable hρ hε ha hweak hL2).1
  let K : ℝ := a / ε
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have htargetMeas : AEStronglyMeasurable
      (fun z => ucGaussianWeight a z * (a / z.2) *
        vec3EuclideanNorm (Z z) ^ 2) μ := by
    have hdiv : Measurable (fun z : ParabolicPoint => a / z.2) := by
      fun_prop
    have h := hdiv.aestronglyMeasurable.mul hW.aestronglyMeasurable
    convert h using 1
    funext z
    dsimp [W]
    ring
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hpoint : ∀ᵐ z ∂μ,
      0 ≤ ucGaussianWeight a z * (a / z.2) *
        vec3EuclideanNorm (Z z) ^ 2 ∧
      ucGaussianWeight a z * (a / z.2) *
        vec3EuclideanNorm (Z z) ^ 2 ≤ K * W z := by
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have hweight := ucGaussianWeight_nonneg a hz.2.1
    have hmass : 0 ≤ W z :=
      mul_nonneg hweight (sq_nonneg _)
    by_cases ht : ε ≤ z.2
    · have hdiv : a / z.2 ≤ K := by
        dsimp [K]
        exact div_le_div_of_nonneg_left ha hε ht
      have hdiv0 : 0 ≤ a / z.2 := div_nonneg ha hz.2.1.le
      constructor
      · positivity
      · have hm := mul_le_mul_of_nonneg_right hdiv hmass
        convert hm using 1
        dsimp [W]
        ring
    · have hzero := uc_cutoff_energy_zero_below hρ hε v Dv z (le_of_lt (lt_of_not_ge ht))
      change Z z = 0 ∧ _ at hzero
      simp [hzero.1, W, vec3EuclideanNorm_zero]
  have hInt : Integrable (fun z => ucGaussianWeight a z * (a / z.2) *
      vec3EuclideanNorm (Z z) ^ 2) μ := by
    apply Integrable.mono_nonneg (hW.const_mul K) htargetMeas
    · exact hpoint.mono (fun z hz => hz.1)
    · exact hpoint.mono (fun z hz => hz.2)
  exact hInt

/-- Both sides of the Gaussian cutoff Carleman inequality are integrable
in product coordinates at positive initial cutoff time. -/
theorem uc_cutoff_carleman_integrable_product
    {ρ ε a : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv
    IntegrableOn (fun z : Vec3 × ℝ =>
      ucGaussianWeight a (parabolicHomeomorph.symm z) * (a / z.2) *
        vec3EuclideanNorm (Z (parabolicHomeomorph.symm z)) ^ 2 +
      ucGaussianWeight a (parabolicHomeomorph.symm z) *
        ∑ i, ∑ j, DZ (parabolicHomeomorph.symm z) i j ^ 2)
      (vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2) volume ∧
    IntegrableOn (fun z : Vec3 × ℝ =>
      ucGaussianWeight a (parabolicHomeomorph.symm z) *
        vec3EuclideanNorm (LZ (parabolicHomeomorph.symm z)) ^ 2)
      (vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2) volume) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv
  have hMass := uc_weighted_cutoff_mass_over_time_integrable hρ hε ha hweak hL2
  change IntegrableOn (fun z => ucGaussianWeight a z * (a / z.2) *
    vec3EuclideanNorm (Z z) ^ 2) (ucCylinder ρ) volume at hMass
  have hGrad := (uc_weighted_cutoff_components_integrable hρ hε ha
    hweak hL2).2
  change IntegrableOn (fun z => ucGaussianWeight a z *
    spatialGradientSq Z DZ z) (ucCylinder ρ) volume at hGrad
  have hHeat := uc_weighted_cutoff_heat_sq_integrable hρ hε ha hweak hL2
  change IntegrableOn (fun z => ucGaussianWeight a z *
    vec3EuclideanNorm (LZ z) ^ 2) (ucCylinder ρ) volume at hHeat
  have hMassP := uc_integrableOn_parabolic_to_product ρ hMass
  have hGradP := uc_integrableOn_parabolic_to_product ρ hGrad
  have hHeatP := uc_integrableOn_parabolic_to_product ρ hHeat
  constructor
  · convert hMassP.add hGradP using 1
    funext z
    dsimp [spatialGradientSq]
  · exact hHeatP

end ESS
