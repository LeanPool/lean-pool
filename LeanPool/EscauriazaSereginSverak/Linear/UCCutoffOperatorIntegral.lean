/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCollarError

/-!
# Integrated cutoff heat inequality

The normalized weak heat inequality separates into an absorbable cutoff
energy, an exponentially damped collar error, and an initial time error.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Classical

noncomputable section

namespace ESS

/-- The heat term in the Gaussian Carleman estimate is bounded by cutoff
energy and the two localized errors (`eq:uc-cutoff-carleman`). -/
theorem uc_cutoff_operator_integral_le
    {ρ ε c₁ scale : ℝ} (hρ : 4 ≤ ρ) (hε : 0 < ε)
    (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    let a := (1 / 100 : ℝ) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
    let A := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
      3 * c₁ * scale * (cutoffGradientConstant / ρ)
    let B := 18 * (cutoffGradientConstant / ρ)
    let Z := ucCutoffField (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv
    let LZ := ucCutoffHeat (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv D2v Dtv
    (∫ z in ucCylinder ρ,
      ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2) ≤
      54 * (c₁ * scale) ^ 2 *
        (∫ z in ucCylinder ρ, ucGaussianWeight a z *
          (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)) +
      (∫ z in ucCylinder ρ, ucGaussianWeight a z *
        (3 * (if z ∈ ucCutoffRegion ρ then
          A * vec3EuclideanNorm (v z) +
            B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)) +
      (192 / ε ^ 2) *
        (∫ z in ucCylinder ρ, ucGaussianWeight a z *
          (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
            vec3EuclideanNorm (v z) ^ 2 else 0)) := by
  dsimp
  have hρpos : 0 < ρ := by linarith only [hρ]
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let A : ℝ := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
    3 * c₁ * scale * (cutoffGradientConstant / ρ)
  let B : ℝ := 18 * (cutoffGradientConstant / ρ)
  let Z := ucCutoffField (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρpos) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv
  let μ := volume.restrict (ucCylinder ρ)
  let F : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2
  let E : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z *
      (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)
  let C : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)
  let I : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0)
  have ha : 0 ≤ a := by
    have hlog := uc_log_weight_three_half_bounds.1
    dsimp [a]
    have hlogpos : 0 < Real.log (gaussCarlemanTimeWeight (3 / 2)) := by
      linarith only [hlog]
    positivity
  have hFInt : Integrable F μ :=
    uc_weighted_cutoff_heat_sq_integrable hρpos hε ha hweak hL2
  have hEInt : Integrable E μ :=
    uc_weighted_cutoff_energy_integrable hρpos hε ha hweak hL2
  have hCInt : Integrable C μ :=
    (uc_gaussian_collar_error_integral_le hρ hweak hL2).1
  have hIInt : Integrable I μ :=
    uc_initial_transition_weighted_sq_integrable hε ha hweak hL2
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hOp := ucGaussianCutoff_operator_sq_ae_bound hρpos hε hc₁ hscale
    v Dv D2v Dtv hineq
  have hPoint : ∀ᵐ z ∂μ,
      F z ≤ 54 * (c₁ * scale) ^ 2 * E z + C z +
        (192 / ε ^ 2) * I z := by
    filter_upwards [hOp, ae_restrict_mem hQmeas] with z hOpz hz
    have hw0 := ucGaussianWeight_nonneg a hz.2.1
    have hm := mul_le_mul_of_nonneg_left (hOpz hz) hw0
    change F z ≤ 54 * (c₁ * scale) ^ 2 * E z + C z +
      (192 / ε ^ 2) * I z
    calc
      F z ≤ ucGaussianWeight a z *
          (54 * (c₁ * scale) ^ 2 *
            (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z) +
          3 * (if z ∈ ucCutoffRegion ρ then
            A * vec3EuclideanNorm (v z) +
              B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2 +
          3 * ((if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
            vec3EuclideanNorm (v z)) ^ 2) := hm
      _ = _ := by
        dsimp only [E, C, I]
        by_cases ht : ε ≤ z.2 ∧ z.2 ≤ 2 * ε
        · simp only [ite_eq_left ht]
          ring
        · simp only [ite_eq_right ht]
          ring
  have hRhsInt : Integrable (fun z =>
      54 * (c₁ * scale) ^ 2 * E z + C z +
        (192 / ε ^ 2) * I z) μ :=
    ((hEInt.const_mul _).add hCInt).add (hIInt.const_mul _)
  have hle := integral_mono_ae hFInt hRhsInt hPoint
  change (∫ z, F z ∂μ) ≤
    54 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
      (∫ z, C z ∂μ) + (192 / ε ^ 2) * (∫ z, I z ∂μ)
  have hsplit : (∫ z, 54 * (c₁ * scale) ^ 2 * E z + C z +
        (192 / ε ^ 2) * I z ∂μ) =
      54 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
        (∫ z, C z ∂μ) + (192 / ε ^ 2) * (∫ z, I z ∂μ) := by
    calc
      _ = (∫ z, 54 * (c₁ * scale) ^ 2 * E z + C z ∂μ) +
          (∫ z, (192 / ε ^ 2) * I z ∂μ) := by
        simpa only [Pi.add_apply] using
          (integral_add ((hEInt.const_mul _).add hCInt)
            (hIInt.const_mul _))
      _ = (∫ z, 54 * (c₁ * scale) ^ 2 * E z ∂μ) +
          (∫ z, C z ∂μ) + (∫ z, (192 / ε ^ 2) * I z ∂μ) := by
        rw [show (∫ z, 54 * (c₁ * scale) ^ 2 * E z + C z ∂μ) =
          (∫ z, 54 * (c₁ * scale) ^ 2 * E z ∂μ) +
            (∫ z, C z ∂μ) from by
              simpa only [Pi.add_apply] using
                (integral_add (hEInt.const_mul _) hCInt)]
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  exact hle.trans_eq hsplit

end ESS
