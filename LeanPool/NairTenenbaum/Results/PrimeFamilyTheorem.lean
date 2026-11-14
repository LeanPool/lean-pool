/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Results.FamilyTheorems
public import LeanPool.NairTenenbaum.Results.TheoremThree

/-! # Theorem 3 for original integer polynomial families

The common irreducible factorization is constructed from the no-fixed-prime
hypothesis. No additional factorization data need be supplied by the caller.
-/

@[expose] public section

namespace NairTenenbaum

/-- The prime-argument main term expressed for the original polynomial family. -/
noncomputable def familyPrimeMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : NoFixedPrimeDivisor (∏ j, Q j)) (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  primeMainTerm (familySystem Q hQ).2 F x y

/-- Theorem 3 with coefficient-independent constants chosen before the
polynomial family. The endpoint range is slightly stronger than the paper's
strict inequality in `ε`. -/
theorem theoremThree_for_families {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k : ℕ) (Q : Fin k → Polynomial ℤ) (hQ : NoFixedPrimeDivisor (∏ j, Q j)),
      (∏ j, Q j).natDegree = g → (∏ j, Q j).eval 0 ≠ 0 →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight (∏ j, Q j) : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      primeShortSum Q F x y ≤ C (familyBadDiscriminant Q hQ) * familyPrimeMainTerm Q hQ F x y := by
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_primeShortSum_mainTerm_bound hg hA hB hε hsmall hδ hδ₁
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro k Q hQ hdeg hzero F hF x y hx hy hyx
  have H' := H k (familySystem Q hQ).1 (familySystem Q hQ).2
    (by simpa only [familySystem_total] using hdeg)
    (by simpa only [familySystem_total] using hzero) F hF x y
    (by simpa only [familySystem_total] using hx) hy hyx
  simpa only [familySystem_Q, familyBadDiscriminant, familyPrimeMainTerm] using H'

end NairTenenbaum
