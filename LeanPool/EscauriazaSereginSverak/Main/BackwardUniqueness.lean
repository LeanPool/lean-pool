/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUConditionalGaussianAssembly
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs

/-!
# Backward uniqueness on a half-space

The Gaussian estimate and its propagation argument prove `thm:bu`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS.Main

/-- Backward uniqueness on a half-space (`thm:bu`; ESS Theorem 5.1). -/
theorem backwardUniqueness (c₁ M : ℝ) (hc₁ : 0 < c₁) (hM : 0 < M)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1), w z = 0 := by
  have hGaussian : ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 12 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (u : ParabolicPoint → Vec3)
          (Du : ParabolicPoint → Fin 3 → Vec3)
          (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
          (Dtu : ParabolicPoint → Vec3),
          ContinuousOn u ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
          (∀ x : Vec3, 0 < x 2 → u (x, 0) = 0) →
          HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
            u Du D2u Dtu →
          (∀ S : Set ParabolicPoint,
            S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
            Bornology.IsBounded S →
            (∫⁻ z in S, ‖Du z‖ₑ ^ (2 : ℝ) +
              ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤) →
          (∀ᵐ z ∂(volume.restrict
            (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
            vec3EuclideanNorm (ucWeakHeatVector D2u Dtu z) ≤
              c₁ * (Real.sqrt (spatialGradientSq u Du z) +
                vec3EuclideanNorm (u z))) →
          (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
            vec3EuclideanNorm (u z) ≤
              Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
          ∀ X : Vec3, 2 < X 2 → ∀ t : ℝ,
            0 < t → t < γ →
            Real.rpow t (-(5 / 2 : ℝ)) *
              (∫ z in spaceTimeSet (Metric.ball X (Real.sqrt (3 * t)))
                (Ioo t (5 * t / 2)),
                vec3EuclideanNorm (u z) ^ 2
                  ∂(volume : Measure ParabolicPoint)) ≤
              C * Real.exp (8 * max A ((1 / (10 : ℝ) ^ 12) / 2) *
                vec3EuclideanNorm X ^ 2) *
                Real.exp (-((1 / (10 : ℝ) ^ 6) * X 2 ^ 2 / (12 * t))) := by
    obtain ⟨γ, hγpos, hγlt, hsource⟩ :=
      ESS.bu_gaussian_average_uniform c₁ hc₁
    refine ⟨γ, hγpos, hγlt, ?_⟩
    intro A hA hAmax
    obtain ⟨C, hCpos, hbound⟩ := hsource A hA hAmax
    refine ⟨C, hCpos, ?_⟩
    intro u Du D2u Dtu hcontU hinitU hderivU hL2U hineqU hgrowthU X hX t ht htγ
    have hpoint := hbound u Du D2u Dtu hcontU hinitU hderivU
      hL2U hineqU hgrowthU X hX t ht htγ
    simpa only [Real.rpow_eq_pow, neg_div] using hpoint
  exact ESS.bu_backwardUniqueness_from_gaussian c₁ M hc₁ hM
    w Dw D2w Dtw hcont hinit hderiv hL2 hineq hgrowth hGaussian

end ESS.Main
