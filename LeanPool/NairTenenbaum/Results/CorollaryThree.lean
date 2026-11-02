/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.FactoredWeightBound
public import LeanPool.NairTenenbaum.Results.TheoremOne

/-! # Corollary 3: products of arithmetic functions on coprime polynomials -/

@[expose] public section

namespace NairTenenbaum

/-- The left side of Corollary 3, with zero extension at polynomial roots. -/
noncomputable def productShortSum {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (F : Fin k → ArithmeticMap 1) (x y : ℝ) : ℝ :=
  ∑ n ∈ shortInterval x y, ∏ j, extendArithmeticMap (F j) (fun _ => ((Q j).eval (n : ℤ)).natAbs)

theorem shortSum_productArithmeticMap {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (F : Fin k → ArithmeticMap 1) (x y : ℝ) :
    shortSum Q (productArithmeticMap F) x y = productShortSum Q F x y := by
  unfold shortSum productShortSum
  exact Finset.sum_congr rfl (fun n _ => extend_productArithmeticMap F _)

/-- Corollary 3, with constants chosen before the polynomial family and the
arithmetic functions. The irreducible factorization data are supplied through
`PolynomialSystem`, as in the current Theorem 1 interface. -/
def CorollaryThree : Prop :=
  ∀ (k g : ℕ), 0 < k → 0 < g →
  ∀ (A B ε δ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      (∀ i j, i ≠ j → IsCoprime ((P.Q i).map (Int.castRingHom ℚ)) ((P.Q j).map (Int.castRingHom
          ℚ))) →
      ∀ (F : Fin k → ArithmeticMap 1), (∀ j, Admissible A B (ε * δ / 3) (F j)) →
      ∀ (x y : ℝ), c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
        productShortSum P.Q F x y ≤ C P.badDiscriminant * factoredMainTerm P F x y

/-- Proof of Corollary 3. The density comparison is applied to entire
substitution fibers, so every original argument is counted only once. -/
theorem corollaryThree : CorollaryThree := by
  intro k g _ hg A B ε δ hA hB hε hsmall hδ hδ₁
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_shortSum_mainTerm_bound hg hA (one_le_pow₀ (n := k) hB)
    hε hsmall' hδ hδ₁
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro r P hdeg hcop F hF x y hx hy hyx
  have Hbound := H k r P hdeg (productArithmeticMap F) (admissible_productArithmeticMap hF) x y hx
      hy hyx
  rw [shortSum_productArithmeticMap] at Hbound
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by
    have H : 0 ≤ c₀ * (polynomialHeight P.total : ℝ) ^ δ := by positivity
    linarith) _).trans hy
  exact Hbound.trans (mul_le_mul_of_nonneg_left
    (P.product_mainTerm_le hcop F (fun j => (hF j).nonneg) x hy₀) (hC P.badDiscriminant).le)

end NairTenenbaum
