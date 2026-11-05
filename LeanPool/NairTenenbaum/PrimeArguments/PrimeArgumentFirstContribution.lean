/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Contributions.FirstContribution
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentMainTerm

/-! # The small-prefix contribution at prime arguments -/

@[expose] public section

namespace NairTenenbaum

/-- The small-prefix contribution restricted to prime arguments above the sieve cutoff. -/
noncomputable def PolynomialSystem.primeSmallRoughContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (a b : ℤ) (z : ℝ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (fun t => P.HasSmallRoughPrefix N z t ∧ t.natAbs.Prime ∧ z <
      t.natAbs),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- The first-contribution reduction, with all counting and roughness inputs
proved and only a total-value upper bound remaining as a hypothesis. -/
theorem PolynomialSystem.primeSmallRoughContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (g : ℕ) (N : ℕ+) (a b : ℤ) {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primeSmallRoughContribution F N a b (x ^ α) ≤
      A ^ (c / α) * P.primeSmallDivisorSiftedSum F g N a b (x ^ α) := by
  classical
  let T := (Finset.Ioc a b).filter (fun t => P.HasSmallRoughPrefix N (x ^ α) t ∧ t.natAbs.Prime ∧
      x ^ α < t.natAbs)
  choose! n q hn using fun t (ht : t ∈ T) => (Finset.mem_filter.mp ht).2.1
  exact P.sum_primeRoughPrefix_le hF hA hB g N a b T n q (Finset.filter_subset _ _)
    (fun t ht => (hn t ht).1) hx hα
    (fun t ht => (Finset.mem_filter.mp ht).2.2.1)
    (fun t ht => (Finset.mem_filter.mp ht).2.2.2) (fun t ht => (hn t ht).2.2)
    (fun t ht => (hn t ht).2.1) (fun t ht => hvalue t (Finset.mem_filter.mp ht).1)

/-- Uniform control of the first class with the logarithmic saving. Only
values of the original total polynomial enter the pointwise growth bound. -/
theorem exists_primeSmallRoughContribution_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε A c : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hA : 1 ≤ A) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.primeSmallRoughContribution F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * primeArgumentSmallSieveCost B σ g P.badDiscriminant * primeMainTerm P F x y := by
  obtain ⟨K, x₁, hK, hx₁, H⟩ := exists_primeSmallDivisorSiftedSum_mainTerm_bound hg hε hsmall
  let C := A ^ (c / ((g : ℝ) * ε / 16))
  have hC : 0 < C := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hA) _
  refine ⟨C * K, max x₁ 2, mul_pos hC hK,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro k r P hdeg hzero B σ F hF hB hσ hσsmall x y N a b hx hN hy hab hlength hlength' hvalue
  have hx₂ : 2 ≤ x := (le_max_right _ _).trans hx
  have hα : 0 < (g : ℝ) * ε / 16 := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have H' := P.primeSmallRoughContribution_le hF hA (zero_le_one.trans hB) g N a b
    (by linarith : 1 < x) hα hvalue
  have H'' := mul_le_mul_of_nonneg_left
    (H k r P hdeg hzero A B σ F hF (zero_le_one.trans hA) hB hσ hσsmall x y N a b
      ((le_max_left _ _).trans hx) hN hy hab hlength hlength') hC.le
  exact H'.trans (by simpa only [C, mul_assoc] using H'')

end NairTenenbaum
