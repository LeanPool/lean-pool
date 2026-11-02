/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SmallDivisorMainTerm
public import LeanPool.NairTenenbaum.Smooth.LargePrefixScales

/-! # The sifted large-prefix sum bounded by the original main term -/

@[expose] public section

namespace NairTenenbaum

/-- The sifted large-prefix sum is bounded by the paper's original main term.
The constants precede the polynomial family and arithmetic function. The interval
endpoint hypotheses allow the natural rounding of a real interval. -/
theorem exists_largePrefixSiftedSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (A B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 0 ≤ A → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      P.smallDivisorSiftedSum F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * mainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hα : 0 < (g : ℝ) * ε / 16 := by positivity
  have hα₁ : (g : ℝ) * ε / 16 ≤ 1 := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
      (sub_nonneg.mpr hg₁))]
  obtain ⟨K, x₁, hK, hx₁, H⟩ := exists_largePrefixSiftedSum_at_scales hg hε
  obtain ⟨x₂, hx₂, Hcut⟩ := exists_sieveProduct_power_cutoff_bound g hα hα₁
  let E := Real.exp (4 * (g : ℝ) * Real.log 4 / ((g : ℝ) * ε / 16))
  refine ⟨2 * K * E, max x₁ x₂, by dsimp [E]; positivity,
    hx₁.trans (le_max_left _ _), ?_⟩
  intro k r P hdeg A B σ F hF hA hB hσ hσsmall x y N a b hx hN hy hab hlength hlength'
  have hx' : 1 ≤ x := hx₁.trans ((le_max_left _ _).trans hx)
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  have hN' : (N : ℝ) ≤ x := hN.trans (by
    have he : 3 * (g : ℝ) ^ 2 * ε ≤ 1 := by linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx' he)
  have hsum : (∑ n ∈ Finset.Icc 1 N, P.weight F n) ≤
      ∑ n ∈ positiveUpTo x, P.weight F n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      apply (mem_positiveUpTo n x).mpr
      exact (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ N).trans hN'
    · intro n _ _
      exact P.weight_nonneg hF.nonneg n
  have hs₀ : 0 ≤ ∑ n ∈ Finset.Icc 1 N, P.weight F n :=
    Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n)
  have hcost := (smallDivisorSieveCost_pos (lt_of_lt_of_le zero_lt_one hB) σ hg
      P.badDiscriminant_pos).le
  have hKC : 0 ≤ K * smallDivisorSieveCost B σ g P.badDiscriminant :=
    mul_nonneg (zero_le_one.trans hK) hcost
  have hS := Hcut x ((le_max_right _ _).trans hx) P.total P.noFixedPrime hdeg.le
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have H' := mul_le_mul hlength' hS (sieveProduct_pos P.noFixedPrime _).le (by
    positivity : 0 ≤ 2 * y)
  have H'' := mul_le_mul H' hsum hs₀
    (mul_nonneg (by
      positivity) (mul_nonneg (Real.exp_nonneg _) (sieveProduct_pos P.noFixedPrime x).le))
  have H''' := mul_le_mul_of_nonneg_left H'' hKC
  apply (H k r P hdeg A B σ F hF hA hB hσ hσsmall x y N a b
    ((le_max_left _ _).trans hx) hN hy hab hlength).trans
  dsimp only [mainTerm, E] at *
  convert H''' using 1 <;> ring

end NairTenenbaum
