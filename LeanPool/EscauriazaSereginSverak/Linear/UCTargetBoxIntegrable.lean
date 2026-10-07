/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetDirectRescale

/-!
# Integrability on the Gaussian target box

The Gaussian weight is integrable on the positive-time box because the
initial cutoff has already reached its plateau there.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Weighted energy of the original field is integrable on a target box
inside the Gaussian cutoff plateau. -/
theorem uc_target_box_weighted_integrable
    {ρ a : ℝ} (hρ : 4 ≤ ρ) (ha : 0 ≤ a)
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
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume := by
  let ε : ℝ := 1 / 8
  have hε : 0 < ε := by norm_num [ε]
  have hεsmall : ε < 1 / 4 := by norm_num [ε]
  have hρpos : 0 < ρ := by linarith only [hρ]
  let Z := ucCutoffField (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  have hBsubQ : B ⊆ ucCylinder ρ := by
    intro z hz
    have hzinner := hbox hz
    have hrad : ρ / 2 ≤ ρ := by linarith only [hρ]
    exact ⟨(vec3Ball_mono hrad) hzinner.1,
      ⟨hzinner.2.1, hzinner.2.2.trans (by norm_num)⟩⟩
  have hEInt : IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z))
      B volume :=
    (uc_weighted_cutoff_energy_integrable hρpos hε ha hweak hL2).mono_set
      hBsubQ
  have hBmeas : MeasurableSet B :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  apply hEInt.congr
  filter_upwards [ae_restrict_mem hBmeas] with z hz
  have hzinner := hbox hz
  have hlate : 2 * ε < z.2 := by
    have htime : 1 / 2 < z.2 := hz.2.1
    dsimp [ε]
    linarith only [htime]
  have hZ := ucGaussianCutoff_field_eq_on_inner_late
    hρpos hε hzinner hlate v
  have hDZ := ucGaussianCutoff_dw_eq_on_inner_late
    hρpos hε hzinner hlate v Dv
  change Z z = v z at hZ
  change DZ z = Dv z at hDZ
  simp only [spatialGradientSq, hZ, hDZ]

end ESS
