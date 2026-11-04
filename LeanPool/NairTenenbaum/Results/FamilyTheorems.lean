/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.FamilyFactorization
public import LeanPool.NairTenenbaum.Results.CorollaryOne
public import LeanPool.NairTenenbaum.Results.CorollaryThree

/-! # The proved estimates for original polynomial families

The factorization data are constructed from the no-fixed-prime hypothesis.
The user of these statements supplies only the original integer polynomials.
All analytic constants precede both the polynomials and their factorization.
-/

@[expose] public section

namespace NairTenenbaum

/-- The restricted discriminant of a selected irreducible factorization. -/
noncomputable def familyBadDiscriminant {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : NoFixedPrimeDivisor (∏ j, Q j)) : ℕ := (familySystem Q hQ).2.badDiscriminant

/-- The original weight main term, with the factorization constructed. -/
noncomputable def familyMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : NoFixedPrimeDivisor (∏ j, Q j)) (F : ArithmeticMap k) (x y : ℝ) : ℝ :=
  mainTerm (familySystem Q hQ).2 F x y

/-- The progression main term, with the factorization constructed. -/
noncomputable def familyProgressionMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : NoFixedPrimeDivisor (∏ j, Q j)) (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) : ℝ :=
  progressionMainTerm (familySystem Q hQ).2 F q x y

/-- Theorem 1 for the original integer polynomials, without an additional
factorization-data hypothesis. The endpoint range in `ε` is slightly stronger
than the paper's strict inequality. -/
theorem theoremOne_for_families {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k : ℕ) (Q : Fin k → Polynomial ℤ) (hQ : NoFixedPrimeDivisor (∏ j, Q j)),
      (∏ j, Q j).natDegree = g → ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight (∏ j, Q j) : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      shortSum Q F x y ≤ C (familyBadDiscriminant Q hQ) * familyMainTerm Q hQ F x y := by
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_shortSum_mainTerm_bound hg hA hB hε hsmall hδ hδ₁
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro k Q hQ hdeg F hF x y hx hy hyx
  have H' := H k (familySystem Q hQ).1 (familySystem Q hQ).2
    (by simpa only [familySystem_total] using hdeg) F hF x y
    (by simpa only [familySystem_total] using hx) hy hyx
  simpa only [familySystem_Q, familyBadDiscriminant, familyMainTerm] using H'

/-- Corollary 1 for original polynomial families. The threshold is chosen
before `β`, and no factorization data need be supplied. The range `δ≤1/2`
contains the paper's range `δ≤1/(2g)`. -/
theorem corollaryOne_for_families {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (k : ℕ) (Q : Fin k → Polynomial ℤ) (hQ : NoFixedPrimeDivisor (∏ j, Q j)),
        (∏ j, Q j).natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → q.Coprime ((∏ j, Q j).eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight (∏ j, Q j) : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum Q F q a x y ≤ C (familyBadDiscriminant Q hQ) *
            familyProgressionMainTerm Q hQ F q x y := by
  obtain ⟨c₁, hc₁, H⟩ := exists_progressionSum_mainTerm_bound hg hA hB hε hsmall hδ hδ₁
  refine ⟨c₁, hc₁, ?_⟩
  intro β hβ hβ₁
  obtain ⟨C, hC, HC⟩ := H β hβ hβ₁
  refine ⟨C, hC, ?_⟩
  intro k Q hQ hdeg F hF q a hq hqa x y hx hy hyx hqty
  have H' := HC k (familySystem Q hQ).1 (familySystem Q hQ).2
    (by simpa only [familySystem_total] using hdeg) F hF q a hq
    (by simpa only [familySystem_total] using hqa) x y
    (by simpa only [familySystem_total] using hx) hy hyx hqty
  simpa only [familySystem_Q, familyBadDiscriminant, familyProgressionMainTerm] using H'

/-- Corollary 3 for original pairwise coprime integer polynomials. Both the
factorization and the reduction to the factored root sums are proved. -/
theorem corollaryThree_for_families {k g : ℕ} (hk : 0 < k) (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : ε < 1 / (8 * (g : ℝ) ^ 2)) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (Q : Fin k → Polynomial ℤ) (hQ : NoFixedPrimeDivisor (∏ j, Q j)),
      (∏ j, Q j).natDegree = g →
      (∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map (Int.castRingHom ℚ))) →
      ∀ (F : Fin k → ArithmeticMap 1), (∀ j, Admissible A B (ε * δ / 3) (F j)) →
      ∀ (x y : ℝ), c₀ * (polynomialHeight (∏ j, Q j) : ℝ) ^ δ < x →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
        productShortSum Q F x y ≤ C (familyBadDiscriminant Q hQ) *
          (y * sieveProduct (∏ j, Q j) x * ∏ j, rootWeightedSum (Q j) (F j) x) := by
  obtain ⟨c₀, hc₀, C, hC, H⟩ := corollaryThree k g hk hg A B ε δ hA hB hε hsmall hδ hδ₁
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro Q hQ hdeg hcop F hF x y hx hy hyx
  have H' := H (familySystem Q hQ).1 (familySystem Q hQ).2
    (by simpa only [familySystem_total] using hdeg)
    (by simpa only [familySystem_Q] using hcop) F hF x y
    (by simpa only [familySystem_total] using hx) hy hyx
  simpa only [familySystem_Q, familyBadDiscriminant, factoredMainTerm, familySystem_total] using H'

end NairTenenbaum
