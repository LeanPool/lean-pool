/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTimeConditional
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortScaleChoice
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortNormalDerivatives

/-!
# Uniform short-time interval

The fixed Carleman constants and Gaussian threshold yield one time
interval valid for every field with the prescribed growth rate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Uniform short-time vanishing follows when the three Gaussian energy
densities are integrable below the Gaussian time threshold
(`lem:bu-small-time`). -/
theorem bu_short_uniform_from_density_provider
    (c₁ γ : ℝ) (hc₁ : 0 < c₁) (hγ : 0 < γ) (hγsmall : γ < 1 / 12)
    (hDensity : ∀ (M scale : ℝ),
      0 < M → M ≤ 1 / (10 : ℝ) ^ 12 →
      (1 / (10 : ℝ) ^ 12) / 2 ≤ M →
      0 < scale → scale ^ 2 ≤ γ →
      ∀ (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3),
        ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1) →
        (∀ x : Vec3, 0 < x 2 → w (x, 0) = 0) →
        HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw →
        (∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) →
        (∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
            c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
              vec3EuclideanNorm (w z))) →
        (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
          vec3EuclideanNorm (w z) ≤
            Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) →
        IntegrableOn (buShortTangentialDensity scale w Dw)
          (buShortWideGapRegion scale) volume ∧
          ∀ a : ℝ, 0 ≤ a →
            IntegrableOn (buShortWeightedPolynomialDensity scale a w Dw)
              (buShortHighStrip scale) volume ∧
            IntegrableOn (buShortWeightedDensity scale a w Dw)
              (buShortHighStrip scale) volume) :
    ∃ γ₁ : ℝ, 0 < γ₁ ∧ γ₁ ≤ γ / 2 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∀ (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3),
        ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1) →
        (∀ x : Vec3, 0 < x 2 → w (x, 0) = 0) →
        HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw →
        (∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) →
        (∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
            c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
              vec3EuclideanNorm (w z))) →
        (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
          vec3EuclideanNorm (w z) ≤
            Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
        ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
          0 < t → t < γ₁ → w (x, t) = 0 := by
  obtain ⟨a₀, c, ha₀, hc, hShort⟩ :=
    bu_short_time_from_integrable_densities
  obtain ⟨C₁, hC₁, hN⟩ := buShortNormalCutoff_abs_deriv_twice_le
  obtain ⟨C₂, hC₂, hP⟩ := bu_short_profile_second_deriv_bound
  obtain ⟨γ₁, hγ₁, hγ₁le, hscale, hscale1, hsmall⟩ :=
    bu_short_scale_choice c c₁ γ hc hγ
  let scale := Real.sqrt (2 * γ₁)
  have hscaleγ : scale ^ 2 ≤ γ := by
    have heq : scale ^ 2 = 2 * γ₁ :=
      Real.sq_sqrt (by positivity : 0 ≤ 2 * γ₁)
    rw [heq]
    linarith only [hγ₁le]
  have hscaleHalf : scale ≤ 1 / 2 := by
    have hquarter : scale ^ 2 ≤ 1 / 4 := by
      linarith only [hscaleγ, hγsmall]
    nlinarith only [hquarter, hscale]
  have hscaleTime : scale ^ 2 / 2 = γ₁ := by
    dsimp [scale]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * γ₁)]
    ring
  refine ⟨γ₁, hγ₁, hγ₁le, ?_⟩
  intro A hA0 hAmax w Dw D2w Dtw
    hcont hinit hweak hL2 hineq hgrowth
  let M := max A ((1 / (10 : ℝ) ^ 12) / 2)
  have hM : 0 < M := by
    dsimp [M]
    exact (by norm_num : (0 : ℝ) < (1 / (10 : ℝ) ^ 12) / 2).trans_le
      (le_max_right _ _)
  have hMmax : M ≤ 1 / (10 : ℝ) ^ 12 := by
    dsimp [M]
    exact max_le hAmax (by norm_num)
  have hgrowthM : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo 0 1), vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2) := by
    intro z hz
    exact (hgrowth z hz).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (sq_nonneg _)))
  obtain ⟨hJ, hWeighted⟩ := hDensity M scale hM hMmax
    (le_max_right _ _) hscale hscaleγ w Dw D2w Dtw
    hcont hinit hweak hL2 hineq hgrowthM
  have hzero := hShort M scale c₁ C₁ C₂ hM hscale hscaleHalf
    hc₁ hC₁ hN hC₂ hP hsmall
    w Dw D2w Dtw hcont hinit hweak hL2 hineq hgrowthM
    hJ (fun a ha => (hWeighted a
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        ((le_max_right a₀ 1).trans ha.le))).1)
    (fun a ha => (hWeighted a
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        ((le_max_right a₀ 1).trans ha.le))).2)
  intro x hx t ht htγ
  exact hzero x hx t ht (by simpa only [hscaleTime] using htγ)

end ESS
