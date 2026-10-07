/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCarlemanBall

/-!
# Gaussian cutoff admissibility

The compact Gaussian cutoff carries all weak derivative and quadratic data
required by the Sobolev Carleman estimate in `lem:uc-gaussian`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The Gaussian cutoff of a field is a compactly supported weak field with
finite quadratic derivative data on the normalized cylinder. -/
theorem ucGaussianCutoff_admissible
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dw D2w Dtw)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v)
      (ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dw)
      (ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dw D2w)
      (ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dtw) ∧
    HasCompactSupport
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v) ∧
    tsupport
      (ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v) ⊆ ucCylinder ρ ∧
    (∫⁻ z in ucCylinder ρ,
      ‖ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v z‖ₑ ^ (2 : ℝ) +
        ‖ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw z‖ₑ ^ (2 : ℝ) +
        ‖ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dw D2w z‖ₑ ^ (2 : ℝ) +
        ‖ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dw
  let D2Z := ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dw D2w
  let DtZ := ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dtw
  have hweakZ : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      Z DZ D2Z DtZ :=
    ucCutoff_hasSpaceTimeWeakDerivs (isOpen_vec3Ball 0 ρ) isOpen_Ioo
      (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff (ucInitialTimeCutoff ε)
      (ucGaussianCutoff_smooth ρ hρ ε) hweak
  have hcompact : HasCompactSupport Z := by
    change HasCompactSupport (ucGaussianCutoff ρ hρ ε • v)
    exact (ucGaussianCutoff_hasCompactSupport hρ hε).smul_right
  have hsupport : tsupport Z ⊆ ucCylinder ρ := by
    intro z hz
    have hsub := tsupport_smul_subset_left (ucGaussianCutoff ρ hρ ε) v
    exact ucGaussianCutoff_tsupport_subset_cylinder hρ hε (hsub hz)
  have hmem := ucGaussianCutoff_l2_data hρ hε hweak hL2
  have hAfin : (∫⁻ z in ucCylinder ρ, ‖Z z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweakZ.1.aestronglyMeasurable).1 hmem.1
    simpa [Z, ucCylinder] using h
  have hBfin : (∫⁻ z in ucCylinder ρ, ‖DZ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweakZ.2.1.aestronglyMeasurable).1 hmem.2.1
    simpa [DZ, ucCylinder] using h
  have hCfin : (∫⁻ z in ucCylinder ρ, ‖D2Z z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweakZ.2.2.1.aestronglyMeasurable).1 hmem.2.2.1
    simpa [D2Z, ucCylinder] using h
  have hDfin : (∫⁻ z in ucCylinder ρ, ‖DtZ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hweakZ.2.2.2.1.aestronglyMeasurable).1 hmem.2.2.2
    simpa [DtZ, ucCylinder] using h
  refine ⟨hweakZ, hcompact, hsupport, ?_⟩
  let μ : Measure ParabolicPoint := volume.restrict (ucCylinder ρ)
  let A : ParabolicPoint → ℝ≥0∞ := fun z => ‖Z z‖ₑ ^ (2 : ℝ)
  let B : ParabolicPoint → ℝ≥0∞ := fun z => ‖DZ z‖ₑ ^ (2 : ℝ)
  let C : ParabolicPoint → ℝ≥0∞ := fun z => ‖D2Z z‖ₑ ^ (2 : ℝ)
  let D : ParabolicPoint → ℝ≥0∞ := fun z => ‖DtZ z‖ₑ ^ (2 : ℝ)
  have hAm : AEMeasurable A μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hweakZ.1.aestronglyMeasurable.enorm
  have hBm : AEMeasurable B μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hweakZ.2.1.aestronglyMeasurable.enorm
  have hCm : AEMeasurable C μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hweakZ.2.2.1.aestronglyMeasurable.enorm
  change (∫⁻ z, (A + B + C) z + D z ∂μ) < ⊤
  rw [lintegral_add_left' ((hAm.add hBm).add hCm)]
  change (∫⁻ z, (A + B) z + C z ∂μ) + (∫⁻ z, D z ∂μ) < ⊤
  rw [lintegral_add_left' (hAm.add hBm)]
  change (∫⁻ z, A z + B z ∂μ) + (∫⁻ z, C z ∂μ) +
    (∫⁻ z, D z ∂μ) < ⊤
  rw [lintegral_add_left' hAm]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩, hCfin⟩, hDfin⟩

end ESS
