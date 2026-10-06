/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCarlemanParabolic

/-!
# Absorbed Gaussian cutoff estimate

The universal Gaussian Carleman constant and a sufficiently small
parabolic scale absorb the weak heat lower order term.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

/-- There is one Gaussian constant for which every normalized cutoff
obeys the absorbed estimate when the lower order scale is small. -/
theorem uc_cutoff_energy_absorbed :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (ρ ε c₁ scale : ℝ) (hρ : 4 ≤ ρ) (hε : 0 < ε)
        (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
        (hsmall : c₀ * 54 * (c₁ * scale) ^ 2 ≤ 1 / 40),
        ∀ (v : ParabolicPoint → Vec3)
          (Dv : ParabolicPoint → Fin 3 → Vec3)
          (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
          (Dtv : ParabolicPoint → Vec3)
          (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
            v Dv D2v Dtv)
          (hL2 : (∫⁻ z in ucCylinder ρ,
          ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
            ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
          (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
            vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
              c₁ * scale * (vec3EuclideanNorm (v z) +
                Real.sqrt (spatialGradientSq v Dv z))),
        let a := (1 / 100 : ℝ) * ρ ^ 2 /
          (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
        let A := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)
        let B := 18 * (cutoffGradientConstant / ρ)
        let Z := ucCutoffField (ucSpatialCutoff ρ (by linarith only [hρ]))
          ucFinalTimeCutoff (ucInitialTimeCutoff ε) v
        let DZ := ucCutoffDw (ucSpatialCutoff ρ (by linarith only [hρ]))
          ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv
        (∫ z in ucCylinder ρ,
          ucGaussianWeight a z *
            (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)) ≤
          40 * c₀ *
            ((∫ z in ucCylinder ρ, ucGaussianWeight a z *
              (3 * (if z ∈ ucCutoffRegion ρ then
                A * vec3EuclideanNorm (v z) +
                  B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)) +
              (192 / ε ^ 2) *
                (∫ z in ucCylinder ρ, ucGaussianWeight a z *
                  (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
                    vec3EuclideanNorm (v z) ^ 2 else 0))) := by
  obtain ⟨c₀, hc₀, hgaussRaw⟩ := ESS.carlemanGaussian
  refine ⟨c₀, hc₀, ?_⟩
  intro ρ ε c₁ scale hρ hε hc₁ hscale hsmall v Dv D2v Dtv hweak hL2 hineq
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
  let E : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)
  let H : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
      ucGaussianWeight a z * spatialGradientSq Z DZ z
  let F : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2
  let C : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)
  let I : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0)
  have ha : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 25)
    (uc_gaussian_exponent_lower_bound hρ)
  have hCar := uc_cutoff_carleman_parabolic_with_constant c₀ hgaussRaw
    hρpos hε hweak hL2 a ha
  change (∫ z, H z ∂μ) ≤ c₀ * (∫ z, F z ∂μ) at hCar
  have hLow := uc_cutoff_carleman_energy_lower hρ hε hweak hL2
  change (1 / 20 : ℝ) * (∫ z, E z ∂μ) ≤ (∫ z, H z ∂μ) at hLow
  have hOp := uc_cutoff_operator_integral_le hρ hε hc₁ hscale hweak hL2 hineq
  change (∫ z, F z ∂μ) ≤
    54 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
      (∫ z, C z ∂μ) + (192 / ε ^ 2) * (∫ z, I z ∂μ) at hOp
  have hQmeas : MeasurableSet (ucCylinder ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hE0 : 0 ≤ ∫ z, E z ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have hgrad : 0 ≤ spatialGradientSq Z DZ z := by
      dsimp [spatialGradientSq]
      positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hz.2.1)
      (add_nonneg (sq_nonneg _) hgrad)
  have hstep : (1 / 20 : ℝ) * (∫ z, E z ∂μ) ≤
      c₀ * (54 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
        (∫ z, C z ∂μ) + (192 / ε ^ 2) * (∫ z, I z ∂μ)) :=
    hLow.trans (hCar.trans
      (mul_le_mul_of_nonneg_left hOp hc₀.le))
  have hcoef : (c₀ * 54 * (c₁ * scale) ^ 2) *
      (∫ z, E z ∂μ) ≤ (1 / 40 : ℝ) * (∫ z, E z ∂μ) :=
    mul_le_mul_of_nonneg_right hsmall hE0
  have hbound : (1 / 20 : ℝ) * (∫ z, E z ∂μ) ≤
      (1 / 40 : ℝ) * (∫ z, E z ∂μ) +
        c₀ * ((∫ z, C z ∂μ) +
          (192 / ε ^ 2) * (∫ z, I z ∂μ)) := by
    calc
      _ ≤ c₀ * (54 * (c₁ * scale) ^ 2 * (∫ z, E z ∂μ) +
        (∫ z, C z ∂μ) + (192 / ε ^ 2) * (∫ z, I z ∂μ)) := hstep
      _ = (c₀ * 54 * (c₁ * scale) ^ 2) * (∫ z, E z ∂μ) +
          c₀ * ((∫ z, C z ∂μ) +
            (192 / ε ^ 2) * (∫ z, I z ∂μ)) := by ring
      _ ≤ _ := add_le_add_left hcoef _
  change (∫ z, E z ∂μ) ≤
    40 * c₀ * ((∫ z, C z ∂μ) +
      (192 / ε ^ 2) * (∫ z, I z ∂μ))
  nlinarith only [hbound]

end ESS
