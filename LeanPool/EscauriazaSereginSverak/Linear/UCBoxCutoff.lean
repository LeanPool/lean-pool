/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialIndicator

/-!
# Target box on the Gaussian cutoff plateau

At target times the compact cutoff equals the original field and its
spatial weak gradient, uniformly for small initial cutoff parameters.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted energy on a target box is bounded by the full weighted
cutoff energy for every sufficiently small initial cutoff. -/
theorem uc_target_box_weighted_le_cutoff_energy
    {ρ ε a : ℝ} (hρ : 4 ≤ ρ) (hε : 0 < ε) (hεsmall : ε < 1 / 4)
    (center : Vec3)
    (hbox : spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1) ⊆
      ucInnerRegion ρ)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (ha : 0 ≤ a) :
    let Z := ucCutoffField (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv
    (∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
      ucGaussianWeight a z *
        (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)) ≤
      ∫ z in ucCylinder ρ, ucGaussianWeight a z *
        (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z) := by
  dsimp
  have hρpos : 0 < ρ := by linarith only [hρ]
  let Z := ucCutoffField (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let E : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)
  let V : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
  have hBmeas : MeasurableSet B :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hBsubQ : B ⊆ ucCylinder ρ := by
    intro z hz
    have hzinner := hbox hz
    have hrad : ρ / 2 ≤ ρ := by linarith only [hρ]
    exact ⟨(vec3Ball_mono hrad) hzinner.1,
      ⟨hzinner.2.1, hzinner.2.2.trans (by norm_num)⟩⟩
  have hEInt : IntegrableOn E (ucCylinder ρ) volume :=
    uc_weighted_cutoff_energy_integrable hρpos hε ha hweak hL2
  have hEpos : 0 ≤ᵐ[volume.restrict (ucCylinder ρ)] E := by
    have hQmeas : MeasurableSet (ucCylinder ρ) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have hgrad : 0 ≤ spatialGradientSq Z DZ z := by
      dsimp [spatialGradientSq]
      positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hz.2.1)
      (add_nonneg (sq_nonneg _) hgrad)
  have hmono : (∫ z in B, E z) ≤ ∫ z in ucCylinder ρ, E z :=
    setIntegral_mono_set hEInt hEpos
      (Filter.Eventually.of_forall (fun _ hz => hBsubQ hz))
  have heq : (∫ z in B, V z) = ∫ z in B, E z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hBmeas] with z hz
    have hzinner := hbox hz
    have hlate : 2 * ε < z.2 := by
      have htime : 1 / 2 < z.2 := hz.2.1
      linarith only [hεsmall, htime]
    have hZ := ucGaussianCutoff_field_eq_on_inner_late
      hρpos hε hzinner hlate v
    have hDZ := ucGaussianCutoff_dw_eq_on_inner_late
      hρpos hε hzinner hlate v Dv
    dsimp [V, E]
    change Z z = v z at hZ
    change DZ z = Dv z at hDZ
    simp only [spatialGradientSq, hZ, hDZ]
  change (∫ z in B, V z) ≤ ∫ z in ucCylinder ρ, E z
  rw [heq]
  exact hmono

end ESS
