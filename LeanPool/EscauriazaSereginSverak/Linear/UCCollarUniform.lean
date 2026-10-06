/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffAbsorbed
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic

/-!
# Uniform collar coefficient

The cutoff derivative constants and the lower order coefficient give a
radius-independent bound on the collar error.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Classical

noncomputable section

namespace ESS

/-- The quadratic collar coefficient is bounded independently of the
normalized radius and of scales at most one. -/
theorem uc_collar_coefficients_uniform
    {ρ c₁ scale : ℝ} (hρ : 4 ≤ ρ)
    (hc₁ : 0 ≤ c₁) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    let A := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
      3 * c₁ * scale * (cutoffGradientConstant / ρ)
    let B := 18 * (cutoffGradientConstant / ρ)
    let M := 32 + 3 * cutoffSecondDerivativeConstant +
      3 * c₁ * cutoffGradientConstant + 18 * cutoffGradientConstant
    0 ≤ A ∧ 0 ≤ B ∧ A ≤ M ∧ B ≤ M := by
  dsimp
  let C₁ : ℝ := cutoffGradientConstant
  let C₂ : ℝ := cutoffSecondDerivativeConstant
  let A : ℝ := 32 + 3 * (C₂ / ρ ^ 2) +
    3 * c₁ * scale * (C₁ / ρ)
  let B : ℝ := 18 * (C₁ / ρ)
  let M : ℝ := 32 + 3 * C₂ + 3 * c₁ * C₁ + 18 * C₁
  have hC₁ : 0 ≤ C₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hC₂ : 0 ≤ C₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hρpos : 0 < ρ := by linarith only [hρ]
  have hρone : 1 ≤ ρ := by linarith only [hρ]
  have hρsqone : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith only [hρ]
  have hC₁div : C₁ / ρ ≤ C₁ := by
    simpa only [div_one] using
      (div_le_div_of_nonneg_left hC₁ (by norm_num : (0 : ℝ) < 1) hρone)
  have hC₂div : C₂ / ρ ^ 2 ≤ C₂ := by
    simpa only [div_one] using
      (div_le_div_of_nonneg_left hC₂ (by norm_num : (0 : ℝ) < 1) hρsqone)
  have hC₁div0 : 0 ≤ C₁ / ρ := div_nonneg hC₁ hρpos.le
  have hC₂div0 : 0 ≤ C₂ / ρ ^ 2 := div_nonneg hC₂ (sq_nonneg ρ)
  have hcscale : c₁ * scale ≤ c₁ := by
    nlinarith only [hc₁, hscale0, hscale1]
  have hterm : c₁ * scale * (C₁ / ρ) ≤ c₁ * C₁ := by
    calc
      c₁ * scale * (C₁ / ρ) ≤ c₁ * (C₁ / ρ) :=
        mul_le_mul_of_nonneg_right hcscale hC₁div0
      _ ≤ c₁ * C₁ := mul_le_mul_of_nonneg_left hC₁div hc₁
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hAle : A ≤ M := by
    dsimp [A, M]
    linarith only [hC₂div, hterm, hC₁]
  have hBle : B ≤ M := by
    dsimp [B, M]
    have hprod : 0 ≤ c₁ * C₁ := mul_nonneg hc₁ hC₁
    linarith only [hC₁div, hC₁, hC₂, hprod]
  exact ⟨hA0, hB0, hAle, hBle⟩

/-- The integrated collar error has a radius-independent coefficient
depending only on the lower order constant. -/
theorem uc_gaussian_collar_error_uniform_integral_le
    {ρ c₁ scale : ℝ} (hρ : 4 ≤ ρ)
    (hc₁ : 0 ≤ c₁) (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1)
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
    let M := 32 + 3 * cutoffSecondDerivativeConstant +
      3 * c₁ * cutoffGradientConstant + 18 * cutoffGradientConstant
    (∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)) ≤
      6 * Real.exp (-(ρ ^ 2) / 100) * M ^ 2 *
        (∫ z in ucCylinder ρ,
          vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z) := by
  dsimp
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let A : ℝ := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
    3 * c₁ * scale * (cutoffGradientConstant / ρ)
  let B : ℝ := 18 * (cutoffGradientConstant / ρ)
  let M : ℝ := 32 + 3 * cutoffSecondDerivativeConstant +
    3 * c₁ * cutoffGradientConstant + 18 * cutoffGradientConstant
  let μ := volume.restrict (ucCylinder ρ)
  let G : ParabolicPoint → ℝ := fun z =>
    A ^ 2 * vec3EuclideanNorm (v z) ^ 2 +
      B ^ 2 * spatialGradientSq v Dv z
  let P : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  obtain ⟨hVInt, hGradInt⟩ := uc_normalized_energy_integrable hweak hL2
  have hGInt : Integrable G μ :=
    (hVInt.const_mul (A ^ 2)).add (hGradInt.const_mul (B ^ 2))
  have hPInt : Integrable P μ := hVInt.add hGradInt
  obtain ⟨hA0, hB0, hAle, hBle⟩ :=
    uc_collar_coefficients_uniform hρ hc₁ hscale0 hscale1
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hC₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    have hC₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
    positivity
  have hAsq : A ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hA0 hM0).2 hAle
  have hBsq : B ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hB0 hM0).2 hBle
  have hpoint (z : ParabolicPoint) : G z ≤ M ^ 2 * P z := by
    have hGrad : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    have hA := mul_le_mul_of_nonneg_right hAsq
      (sq_nonneg (vec3EuclideanNorm (v z)))
    have hB := mul_le_mul_of_nonneg_right hBsq hGrad
    dsimp [G, P]
    nlinarith only [hA, hB]
  have hmono : (∫ z, G z ∂μ) ≤ M ^ 2 * (∫ z, P z ∂μ) := by
    have h := integral_mono_ae hGInt (hPInt.const_mul (M ^ 2))
      (Filter.Eventually.of_forall hpoint)
    simpa only [integral_const_mul] using h
  have hC := (uc_gaussian_collar_error_integral_le
    (c₁ := c₁) (scale := scale) hρ hweak hL2).2
  change (∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        A * vec3EuclideanNorm (v z) +
          B * Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)) ≤
      6 * Real.exp (-(ρ ^ 2) / 100) * M ^ 2 * (∫ z, P z ∂μ)
  calc
    _ ≤ 6 * Real.exp (-(ρ ^ 2) / 100) * (∫ z, G z ∂μ) := hC
    _ ≤ 6 * Real.exp (-(ρ ^ 2) / 100) *
        (M ^ 2 * (∫ z, P z ∂μ)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by ring

end ESS
