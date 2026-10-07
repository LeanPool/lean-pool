/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffOperatorIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffCarleman

/-!
# Absorption in the Gaussian cutoff estimate

The Carleman mass coefficient has a uniform positive lower bound when
the normalized spatial radius is at least four.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian exponent selected from the cutoff radius is uniformly
positive for radii at least four. -/
theorem uc_gaussian_exponent_lower_bound
    {ρ : ℝ} (hρ : 4 ≤ ρ) :
    (3 / 25 : ℝ) ≤ (1 / 100) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2))) := by
  let L : ℝ := Real.log (gaussCarlemanTimeWeight (3 / 2))
  have hLlo : 1 / 5 ≤ L := uc_log_weight_three_half_bounds.1
  have hLhi : L ≤ 2 / 3 := uc_log_weight_three_half_bounds.2
  have hLpos : 0 < L := by linarith only [hLlo]
  have hρsq : 16 ≤ ρ ^ 2 := by nlinarith only [hρ]
  apply (le_div_iff₀ (by positivity : 0 < 2 * L)).2
  dsimp [L] at *
  nlinarith only [hρsq, hLhi]

/-- The positive Carleman field and gradient terms control one twentieth
of the weighted cutoff energy on the normalized cylinder. -/
theorem uc_cutoff_carleman_energy_lower
    {ρ ε : ℝ} (hρ : 4 ≤ ρ) (hε : 0 < ε)
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
    let Z := ucCutoffField (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv
    (1 / 20 : ℝ) *
      (∫ z in ucCylinder ρ, ucGaussianWeight a z *
        (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)) ≤
      (∫ z in ucCylinder ρ,
        ucGaussianWeight a z * (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
          ucGaussianWeight a z * spatialGradientSq Z DZ z) := by
  dsimp
  have hρpos : 0 < ρ := by linarith only [hρ]
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let Z := ucCutoffField (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let μ := volume.restrict (ucCylinder ρ)
  let E : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)
  let H : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
      ucGaussianWeight a z * spatialGradientSq Z DZ z
  have ha : 0 ≤ a := (uc_gaussian_exponent_lower_bound hρ).trans'
    (by norm_num : (0 : ℝ) ≤ 3 / 25)
  have hEInt : Integrable E μ :=
    uc_weighted_cutoff_energy_integrable hρpos hε ha hweak hL2
  have hMassInt := uc_weighted_cutoff_mass_over_time_integrable
    hρpos hε ha hweak hL2
  have hGradInt := (uc_weighted_cutoff_components_integrable
    hρpos hε ha hweak hL2).2
  have hHInt : Integrable H μ := hMassInt.add hGradInt
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hpoint : ∀ᵐ z ∂μ, (1 / 20 : ℝ) * E z ≤ H z := by
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have ha' : 3 / 25 ≤ a := uc_gaussian_exponent_lower_bound hρ
    have hcoef : (1 / 20 : ℝ) ≤ a / z.2 := by
      have hhalf : a / 2 ≤ a / z.2 :=
        div_le_div_of_nonneg_left ha hz.2.1 hz.2.2.le
      have hlow : (1 / 20 : ℝ) ≤ a / 2 := by linarith only [ha']
      exact hlow.trans hhalf
    have hgrad : 0 ≤ spatialGradientSq Z DZ z := by
      dsimp [spatialGradientSq]
      positivity
    have hmass : (1 / 20 : ℝ) * vec3EuclideanNorm (Z z) ^ 2 ≤
        (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    have hgrad' : (1 / 20 : ℝ) * spatialGradientSq Z DZ z ≤
        spatialGradientSq Z DZ z := by
      nlinarith only [hgrad]
    have hweight := ucGaussianWeight_nonneg a hz.2.1
    dsimp [E, H]
    have hsum : (1 / 20 : ℝ) *
        (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z) ≤
      (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
        spatialGradientSq Z DZ z := by
      nlinarith only [hmass, hgrad']
    have := mul_le_mul_of_nonneg_left hsum hweight
    nlinarith only [this]
  have hle := integral_mono_ae (hEInt.const_mul (1 / 20)) hHInt hpoint
  simpa only [integral_const_mul] using hle

end ESS
