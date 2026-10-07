/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortGaussianDensities
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUniformConditional

/-!
# Uniform short-time vanishing from Gaussian averages

The Gaussian averaging lemma supplies the three integrable densities
needed by the half-space Carleman argument.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The Gaussian averaging estimate implies a uniform short-time
vanishing interval (`lem:bu-small-time`). -/
theorem bu_short_uniform_of_gaussian
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hGaussian : ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 12 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (w : ParabolicPoint → Vec3)
          (Dw : ParabolicPoint → Fin 3 → Vec3)
          (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
          (Dtw : ParabolicPoint → Vec3),
          ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
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
          ∀ X : Vec3, 2 < X 2 → ∀ t : ℝ,
            0 < t → t < γ →
            Real.rpow t (-(5 / 2 : ℝ)) *
              (∫ z in spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
                (Ioo t (5 * t / 2)),
                vec3EuclideanNorm (w z) ^ 2
                  ∂(volume : Measure ParabolicPoint)) ≤
              C * Real.exp (8 * max A ((1 / (10 : ℝ) ^ 12) / 2) *
                vec3EuclideanNorm X ^ 2) *
                Real.exp (-((1 / (10 : ℝ) ^ 6) * X 2 ^ 2 / (12 * t)))) :
    ∃ γ γ₁ : ℝ,
      0 < γ ∧ γ < 1 / 12 ∧ 0 < γ₁ ∧ γ₁ ≤ γ / 2 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∀ (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3),
        ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
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
  obtain ⟨γ, hγ, hγsmall, hBound⟩ := hGaussian
  obtain ⟨γ₁, hγ₁, hγ₁le, hShort⟩ :=
    bu_short_uniform_from_density_provider c₁ γ hc₁ hγ hγsmall
      (by
        intro M scale hM hMmax hMbar hscale hscaleγ
          w Dw D2w Dtw hcont hinit hweak hL2 hineq hgrowth
        obtain ⟨C, hC, hGauss⟩ := hBound M hM.le hMmax
        have hGaussianField := hGauss w Dw D2w Dtw
          hcont hinit hweak hL2 hineq hgrowth
        have hAt (a : ℝ) (ha : 0 ≤ a) :=
          bu_short_densities_from_gaussian M scale γ C c₁ a
            hMmax hMbar hscale hscaleγ hγsmall hC hc₁ ha
            w Dw D2w Dtw hcont hweak hL2 hineq hgrowth
            hGaussianField
        have hJ : IntegrableOn
            (buShortTangentialDensity scale w Dw)
            (buShortWideGapRegion scale) volume :=
          (hAt 0 (by norm_num)).1.mono_set
            (buShortWideGapRegion_subset_highStrip scale)
        exact ⟨hJ, fun a ha => ⟨(hAt a ha).2.1, (hAt a ha).2.2⟩⟩)
  exact ⟨γ, γ₁, hγ, hγsmall, hγ₁, hγ₁le, hShort⟩

end ESS
