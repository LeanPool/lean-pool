/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.IrreducibleProgressionWeights
public import LeanPool.NairTenenbaum.Results.CorollaryOne

/-! # Corollary 2: the explicit irreducible-coordinate progression bound -/

@[expose] public section

namespace NairTenenbaum

/-- Corollary 2, equation (20). Integral irreducibility is assumed; coprimality
of polynomials is expressed over the rational coefficient field. The
factorization data are constructed rather than supplied as an extra input. -/
def CorollaryTwo : Prop :=
  ∀ (k g : ℕ), 0 < k → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 / (2 * (g : ℝ)) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (Q : Fin k → Polynomial ℤ), (∀ j, Irreducible (Q j)) →
        (∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map (Int.castRingHom ℚ))) →
        NoFixedPrimeDivisor (∏ j, Q j) → (∏ j, Q j).natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → 0 < a → a ≤ q → q.Coprime ((∏ j, Q j).eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight (∏ j, Q j) : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum Q F q a x y ≤ C (irreducibleBadDiscriminant Q) *
            irreducibleProgressionMainTerm Q F q x y

/-- Proof of Corollary 2, with the exact tuple main term and the same
uniformity in coefficients, restricted discriminant, and progression data. -/
theorem corollaryTwo : CorollaryTwo := by
  intro k g hk hg A B ε δ hA hB hε hsmall hδ hδg
  obtain ⟨c₀, hc₀, H⟩ := corollaryOne k k g hk hk hg A B ε δ hA hB hε hsmall hδ hδg
  refine ⟨c₀, hc₀, ?_⟩
  intro β hβ hβ₁
  obtain ⟨C, hC, HC⟩ := H β hβ hβ₁
  refine ⟨C, hC, ?_⟩
  intro Q hI hcoprime hfixed hdeg F hF q a hq ha haq hqa x y hx hy hyx hqty
  have hR (j : Fin k) : Irreducible ((Q j).map (Int.castRingHom ℚ)) :=
    (hfixed.of_dvd (Finset.dvd_prod_of_mem Q (Finset.mem_univ j))).irreducible_map (hI j)
  let P := PolynomialSystem.ofIrreducible Q hR hcoprime hfixed
  have Hbound := HC P hdeg F hF q a hq ha haq hqa x y hx hy hyx hqty
  change progressionSum Q F q a x y ≤ C P.badDiscriminant * progressionMainTerm P F q x y at Hbound
  simpa only [P, PolynomialSystem.ofIrreducible_badDiscriminant,
    ofIrreducible_progressionMainTerm Q hR hcoprime hfixed F q x y] using Hbound

end NairTenenbaum
