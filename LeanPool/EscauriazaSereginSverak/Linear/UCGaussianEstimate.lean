/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCSourceBox
public import LeanPool.EscauriazaSereginSverak.Linear.UCNormalize
public import LeanPool.EscauriazaSereginSverak.Linear.UCRadiusGeometry

/-!
# Gaussian propagation from integral flatness

The normalized Carleman estimate and parabolic rescaling yield the
positive-time Gaussian box estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Integral vanishing at a center yields Gaussian decay on nearby
positive-time boxes (`lem:uc-gaussian`). -/
theorem uc_gaussian_box_estimate
    (R T c₁ : ℝ) (hR : 0 < R) (hT : 0 < T) (hT1 : T ≤ 1)
    (hc₁ : 0 < c₁) (x₀ : Vec3)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (vec3Ball x₀ R ×ˢ Ico 0 T))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)))
    (hflat : UCIntegralFlatness x₀ R T w) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 3 / 16 ∧ 0 < C ∧
      ∀ (x : Vec3) (t : ℝ), 0 < t → t ≤ γ * T →
        vec3EuclideanNorm (x - x₀) ≤ ucRadiusFraction * R →
        (16 / 100) * t ≤ vec3EuclideanNorm (x - x₀) ^ 2 →
        (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
          (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
          C * ucLocalEnergy x₀ R T w Dw *
            Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hweighted⟩ :=
    uc_gaussian_weighted_target_box c₁ hc₁.le
  obtain ⟨γ, hγ, hγsmall, hsmall⟩ :=
    uc_gaussian_small_scale c₀ c₁ hc₀ hc₁
  let C : ℝ := 2 * Real.exp 1 * C₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨γ, C, hγ, hγsmall, hC, ?_⟩
  intro x t ht htγ hx hd
  let scale : ℝ := Real.sqrt (2 * t)
  let ρ : ℝ := 2 * vec3EuclideanNorm
    ((Real.sqrt (2 / 100))⁻¹ • (x - x₀)) / scale
  let a : ℝ := (1 / 100) * ρ ^ 2 /
    (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))
  let center : Vec3 := scale⁻¹ • (x - x₀)
  let v := ucScaledField x₀ scale w
  let Dv := ucScaledDw x₀ scale Dw
  let D2v := ucScaledD2w x₀ scale D2w
  let Dtv := ucScaledDtw x₀ scale Dtw
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hscaleSq : scale ^ 2 = 2 * t := by
    dsimp [scale]
    rw [Real.sq_sqrt (by positivity)]
  have hx' : vec3EuclideanNorm (x - x₀) ≤
      (3 / 8) * Real.sqrt (2 / 100) * R := by
    simpa only [ucRadiusFraction] using hx
  have hnorm := uc_gaussian_normalize_and_scale R T γ c₁
    hR hT hγsmall hT1 hc₁ x₀ x t ht htγ hx' hd
    w Dw D2w Dtw hcont hweak hL2 hineq hflat
  change 4 ≤ ρ ∧ scale * ρ ≤ 3 * R / 4 ∧
      2 * scale ^ 2 ≤ 3 * T / 4 ∧
      HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
        v Dv D2v Dtv ∧
      (∫⁻ z in ucCylinder ρ,
        ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      UCIntegralFlatness 0 ρ 2 v ∧
      (∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
        vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
          c₁ * scale * (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) at hnorm
  rcases hnorm with ⟨hρ, hball, htime, hweakv, hL2v, hflatv, hineqv⟩
  have hscale1 : scale ≤ 1 := by
    have hs : scale ^ 2 ≤ 3 / 8 := by linarith only [htime, hT1]
    nlinarith only [hscale, hs]
  have hsmall' : c₀ * 54 * (c₁ * scale) ^ 2 ≤ 1 / 40 :=
    hsmall T t scale hT hT1 ht htγ hscaleSq
  have hbox : spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1) ⊆
      ucInnerRegion ρ :=
    uc_target_box_subset_inner x₀ x scale ρ hscale hρ rfl
  have ha : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 3 / 25).trans
    (uc_gaussian_exponent_lower_bound hρ)
  have hweightedInt : IntegrableOn
      (fun z => ucGaussianWeight a z *
        (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume :=
    uc_target_box_weighted_integrable hρ ha center hbox hweakv hL2v
  have hweighted' := hweighted ρ scale hρ hscale.le hscale1 hsmall'
    center hbox v Dv D2v Dtv hweakv hL2v hineqv hflatv
  change (∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
      ucGaussianWeight a z *
        (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)) ≤
      C₀ * Real.exp (-(ρ ^ 2) / 100) *
        (∫ z in ucCylinder ρ,
          vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z) at hweighted'
  have hboxQ : spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1) ⊆
      ucCylinder ρ := by
    intro z hz
    have hzinner := hbox hz
    have hrad : ρ / 2 ≤ ρ := by linarith only [hρ]
    exact ⟨(vec3Ball_mono hrad) hzinner.1,
      ⟨hzinner.2.1, hzinner.2.2.trans (by norm_num)⟩⟩
  have hboxInt : IntegrableOn
      (fun z => vec3EuclideanNorm (v z) ^ 2)
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume :=
    (uc_normalized_energy_integrable hweakv hL2v).1.mono_set hboxQ
  let S := spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)
  have hL2w : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S,
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) := by
            apply lintegral_mono
            intro z
            exact le_add_of_nonneg_right (by positivity) |>.trans
              (le_add_of_nonneg_right (by positivity) |>.trans
                (le_add_of_nonneg_right (by positivity)))
      _ < ⊤ := hL2
  have hsource : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t))) volume :=
    uc_squared_norm_integrable_on_subset S _ w hweak.1 hL2w
      (uc_source_target_box_subset R T scale ρ t hR hT hscale hρ
        hball htime hscaleSq x₀ x hx')
  have hL2two : (∫⁻ z in S,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S,
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ) := by
            apply lintegral_mono
            intro z
            exact le_add_of_nonneg_right (by positivity) |>.trans
              (le_add_of_nonneg_right (by positivity))
      _ < ⊤ := hL2
  have henergy := uc_gaussian_energy_rescaling R T scale ρ
    hR hT hscale hball htime x₀ w Dw D2w Dtw hweak hL2two
  have hresult := uc_gaussian_target_box_direct_rescaling x₀ x
    R T t ρ scale a C₀ ht rfl hρ hC₀ rfl rfl w Dw
    hsource hboxInt hweightedInt hweighted' henergy
  change (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
      (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
      C * ucLocalEnergy x₀ R T w Dw *
        Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t))
  exact hresult

end ESS
