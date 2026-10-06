/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCBoxCutoff

/-!
# Weighted Gaussian target box

Absorption, collar decay, and the vanishing initial time error yield a
weighted estimate directly on the positive-time target box.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Classical Topology

noncomputable section

namespace ESS

/-- A fixed Gaussian constant gives a uniform weighted target-box bound
for every sufficiently small normalized lower order scale. -/
theorem uc_gaussian_weighted_target_box
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ (ρ scale : ℝ) (_hρ : 4 ≤ ρ)
        (_hscale0 : 0 ≤ scale) (_hscale1 : scale ≤ 1)
        (_hsmall : c₀ * 54 * (c₁ * scale) ^ 2 ≤ 1 / 40)
        (center : Vec3)
        (_hbox : spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1) ⊆
          ucInnerRegion ρ)
        (v : ParabolicPoint → Vec3)
        (Dv : ParabolicPoint → Fin 3 → Vec3)
        (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtv : ParabolicPoint → Vec3)
        (_hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
          v Dv D2v Dtv)
        (_hL2 : (∫⁻ z in ucCylinder ρ,
          ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
            ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
        (_hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
          vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
            c₁ * scale * (vec3EuclideanNorm (v z) +
              Real.sqrt (spatialGradientSq v Dv z)))
        (_hflat : UCIntegralFlatness 0 ρ 2 v),
        let a := (1 / 100 : ℝ) * ρ ^ 2 /
          (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
        (∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
          ucGaussianWeight a z *
            (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)) ≤
          C₀ * Real.exp (-(ρ ^ 2) / 100) *
            (∫ z in ucCylinder ρ,
              vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z) := by
  obtain ⟨c₀, hc₀, hAbs⟩ := uc_cutoff_energy_absorbed
  let M : ℝ := 32 + 3 * cutoffSecondDerivativeConstant +
    3 * c₁ * cutoffGradientConstant + 18 * cutoffGradientConstant
  have hM : 0 < M := by
    have hC₁ := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    have hC₂ := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
    dsimp [M]
    positivity
  let C₀ : ℝ := 240 * c₀ * M ^ 2
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨c₀, C₀, hc₀, hC₀, ?_⟩
  intro ρ scale hρ hscale0 hscale1 hsmall center hbox
    v Dv D2v Dtv hweak hL2 hineq hflat
  dsimp
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let μ := volume.restrict (ucCylinder ρ)
  let P : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let W : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z * P z
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let K : ℝ := Real.exp (-(ρ ^ 2) / 100)
  have ha : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 3 / 25).trans
    (uc_gaussian_exponent_lower_bound hρ)
  have hEarly := uc_initial_indicator_error_tendsto_zero
    hρ ha hweak hL2 hflat
  let J : ℝ := ∫ z in B, W z
  let E : ℝ := ∫ z in ucCylinder ρ, P z
  let err (ε : ℝ) : ℝ := (192 / ε ^ 2) *
    (∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0))
  change Tendsto err (𝓝[>] (0 : ℝ)) (𝓝 0) at hEarly
  have hlim : Tendsto (fun ε : ℝ => 40 * c₀ * (6 * K * M ^ 2 * E + err ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (40 * c₀ * (6 * K * M ^ 2 * E))) := by
    convert (tendsto_const_nhds.add hEarly).const_mul (40 * c₀) using 1 ;
      ring_nf
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 4 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      J ≤ 40 * c₀ * (6 * K * M ^ 2 * E + err ε) := by
    filter_upwards [self_mem_nhdsWithin, hεsmall] with ε hε hεsmall
    have hBox := uc_target_box_weighted_le_cutoff_energy
      hρ hε hεsmall center hbox hweak hL2 ha
    have hAbsε := hAbs ρ ε c₁ scale hρ hε hc₁ hscale0 hsmall
      v Dv D2v Dtv hweak hL2 hineq
    have hCollar := uc_gaussian_collar_error_uniform_integral_le
      hρ hc₁ hscale0 hscale1 hweak hL2
    let Z := ucCutoffField (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ (by linarith only [hρ]))
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) v Dv
    let CE : ℝ := ∫ z in ucCylinder ρ,
      ucGaussianWeight a z *
        (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z)
    let CErr : ℝ := ∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (3 * (if z ∈ ucCutoffRegion ρ then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) ^ 2)
    change J ≤ CE at hBox
    change CE ≤ 40 * c₀ * (CErr + err ε) at hAbsε
    change CErr ≤ 6 * K * M ^ 2 * E at hCollar
    have hcoef : 0 ≤ 40 * c₀ := by positivity
    calc
      J ≤ CE := hBox
      _ ≤ 40 * c₀ * (CErr + err ε) := hAbsε
      _ ≤ 40 * c₀ * (6 * K * M ^ 2 * E + err ε) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hCollar _) hcoef
  have hfinal : J ≤ 40 * c₀ * (6 * K * M ^ 2 * E) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
  change J ≤ C₀ * K * E
  calc
    J ≤ 40 * c₀ * (6 * K * M ^ 2 * E) := hfinal
    _ = C₀ * K * E := by dsimp [C₀]; ring

end ESS
