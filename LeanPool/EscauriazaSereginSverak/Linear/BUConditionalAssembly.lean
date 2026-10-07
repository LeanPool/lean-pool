/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BULargeGrowth

/-!
# Assembly of backward uniqueness from short-time vanishing

The small-growth iteration and finite-slab rescaling reduce `thm:bu` to
the uniform short-time result `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The exact backward-uniqueness conclusion follows from the uniform
short-time vanishing lemma. -/
theorem bu_backwardUniqueness_from_short
    (c₁ M : ℝ) (hc₁ : 0 < c₁) (hM : 0 < M)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (Real.sqrt (spatialGradientSq w Dw z) +
          vec3EuclideanNorm (w z)))
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    (hshort : ∃ γ γ₁ : ℝ,
      0 < γ ∧ γ < 1 / 12 ∧ 0 < γ₁ ∧ γ₁ ≤ γ / 2 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∀ (v : ParabolicPoint → Vec3)
        (Dv : ParabolicPoint → Fin 3 → Vec3)
        (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtv : ParabolicPoint → Vec3),
        ContinuousOn v ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) →
        (∀ x : Vec3, 0 < x 2 → v (x, 0) = 0) →
        HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          v Dv D2v Dtv →
        (∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ) +
            ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) →
        (∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
          vec3EuclideanNorm (fun i => Dtv z i + ∑ j, D2v z i j j) ≤
            c₁ * (Real.sqrt (spatialGradientSq v Dv z) +
              vec3EuclideanNorm (v z))) →
        (∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
          vec3EuclideanNorm (v z) ≤
            Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
        ∀ x : Vec3, 0 < x 2 → ∀ s : ℝ,
          0 < s → s < γ₁ → v (x, s) = 0) :
    ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1), w z = 0 := by
  obtain ⟨γ, γ₁, hγ0, hγsmall, hγ₁0, hγ₁le, hshort⟩ := hshort
  have hγ₁one : γ₁ < 1 := by
    nlinarith only [hγsmall, hγ₁le]
  have hsmallFull (A : ℝ) (hA0 : 0 ≤ A)
      (hA1 : A ≤ 1 / (10 : ℝ) ^ 12)
      (v : ParabolicPoint → Vec3)
      (Dv : ParabolicPoint → Fin 3 → Vec3)
      (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
      (Dtv : ParabolicPoint → Vec3)
      (hvcont : ContinuousOn v ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
      (hvinit : ∀ x : Vec3, 0 < x 2 → v (x, 0) = 0)
      (hvderiv : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
        v Dv D2v Dtv)
      (hvL2 : ∀ S : Set ParabolicPoint,
        S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
        Bornology.IsBounded S →
        (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ) +
          ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
      (hvineq : ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1))),
        vec3EuclideanNorm (fun i => Dtv z i + ∑ j, D2v z i j j) ≤
          c₁ * (Real.sqrt (spatialGradientSq v Dv z) +
            vec3EuclideanNorm (v z)))
      (hvgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
        vec3EuclideanNorm (v z) ≤
          Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) :
      ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
        0 < t → t < 1 → v (x, t) = 0 := by
    exact bu_time_iteration_from_short c₁ A γ₁ hc₁ hA0 hγ₁0 hγ₁one
      v Dv D2v Dtv hvcont hvinit hvderiv hvL2 hvineq hvgrowth
      (hshort A hA0 hA1)
  have hzero : ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < 1 → w (x, t) = 0 := by
    by_cases hMsmall : M ≤ 1 / (10 : ℝ) ^ 12
    · exact hsmallFull M hM.le hMsmall w Dw D2w Dtw
        hcont hinit hderiv hL2 hineq hgrowth
    · have hAlarge : (1 / (10 : ℝ) ^ 12) < M := lt_of_not_ge hMsmall
      have hAhalf0 : 0 ≤ (1 / (10 : ℝ) ^ 12) / 2 := by positivity
      have hAhalf1 : (1 / (10 : ℝ) ^ 12) / 2 ≤
          1 / (10 : ℝ) ^ 12 := by norm_num
      exact bu_large_growth_from_small c₁ M hc₁ hAlarge
        w Dw D2w Dtw hcont hinit hderiv hL2 hineq hgrowth
        (hsmallFull ((1 / (10 : ℝ) ^ 12) / 2) hAhalf0 hAhalf1)
  exact bu_backwardUniqueness_from_halfSpaceConclusion hzero

end ESS
