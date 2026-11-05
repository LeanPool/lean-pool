/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Progressions.ProgressionBound

/-! # Corollary 1: short sums in arithmetic progressions -/

@[expose] public section

namespace NairTenenbaum

/-- Corollary 1 with the coefficient-height threshold independent of `β`, the
arithmetic growth exponent `εβδ/6`, and both omitted-prime restrictions in the
main term. As in Theorem 1, the irreducible factorization data are supplied. -/
def CorollaryOne : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 / (2 * (g : ℝ)) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ β : ℝ, 0 < β → β < 1 →
      ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
        ∀ (P : PolynomialSystem k r), P.total.natDegree = g →
        ∀ (F : ArithmeticMap k), Admissible A B (ε * β * δ / 6) F →
        ∀ (q a : ℕ), 0 < q → 0 < a → a ≤ q → q.Coprime (P.total.eval (a : ℤ)).natAbs →
        ∀ (x y : ℝ), c₁ * (polynomialHeight P.total : ℝ) ^ (2 * δ) < x →
          x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → (q : ℝ) ≤ y ^ (1 - β) →
          progressionSum P.Q F q a x y ≤ C P.badDiscriminant * progressionMainTerm P F q x y

/-- Proof of Corollary 1. The argument retains the original scale after affine
substitution and uses the exact transformed weight and Euler-product identities. -/
theorem corollaryOne : CorollaryOne := by
  intro k r g _ _ hg A B ε δ hA hB hε hsmall hδ hδg
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  have hδ₁ : δ ≤ 1 / 2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2 * (g : ℝ))).mp hδg
    nlinarith [mul_le_mul_of_nonneg_left hg₁ hδ.le]
  obtain ⟨c₁, hc₁, H⟩ := exists_progressionSum_mainTerm_bound hg hA hB hε hsmall' hδ hδ₁
  refine ⟨c₁, hc₁, ?_⟩
  intro β hβ hβ₁
  obtain ⟨C, hC, HC⟩ := H β hβ hβ₁
  refine ⟨C, hC, ?_⟩
  intro P hdeg F hF q a hq _ _ hqa x y hx hy hyx hqty
  exact HC k r P hdeg F hF q a hq hqa x y hx hy hyx hqty

end NairTenenbaum
