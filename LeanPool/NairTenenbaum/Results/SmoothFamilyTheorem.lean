/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Results.CorollarySix
public import LeanPool.NairTenenbaum.Results.FamilyTheorems

/-! # Corollary 6 for the original polynomial family -/

@[expose] public section

namespace NairTenenbaum

/-- The smoothness estimate with the common factorization constructed from
the no-fixed-prime condition. The restricted coordinate is nonconstant. -/
theorem corollarySix_for_families {g : ℕ} (hg : 0 < g) {A B ε δ κ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hκ : 0 < κ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k : ℕ) (Q : Fin k → Polynomial ℤ) (hQ : NoFixedPrimeDivisor (∏ j, Q j)),
      (∏ j, Q j).natDegree = g → ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 4) F →
      ∀ (j : Fin k), 0 < (Q j).natDegree → ∀ (x y z : ℝ),
      c₀ * (polynomialHeight (∏ j, Q j) : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      (2 : ℝ) ^ (κ / (2 * (g : ℝ) ^ 2 * ε)) ≤ z → z ≤ x →
      smoothShortSum Q F j x y z ≤ C (familyBadDiscriminant Q hQ) *
        Real.exp (-κ * Real.log x / Real.log z) * familyMainTerm Q hQ F x y := by
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_smoothShortSum_mainTerm_bound hg hA hB hε hsmall hδ hδ₁ hκ
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro k Q hQ hdeg F hF j hj x y z hx hy hyx hz hzx
  have H' := H k (familySystem Q hQ).1 (familySystem Q hQ).2
    (by simpa only [familySystem_total] using hdeg) F hF j
    (by simpa only [familySystem_Q] using hj) x y z
    (by simpa only [familySystem_total] using hx) hy hyx hz hzx
  simpa only [familySystem_Q, familyBadDiscriminant, familyMainTerm] using H'

end NairTenenbaum
