/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.IntegerIntervalBound
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentHeight
public import LeanPool.NairTenenbaum.Results.Targets

/-! # Theorem 1: short sums of admissible arithmetic functions

The four majorants give a coefficient-independent height threshold and a bound
constant depending only on the fixed parameters and the restricted discriminant.
The bad-prime corrections retain all valuations throughout the proof.
-/

@[expose] public section

namespace NairTenenbaum

/-- The short-sum estimate, with constants uniform also in the number of
polynomials and irreducible factors at fixed total degree. -/
theorem exists_shortSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 3) F →
      ∀ x y : ℝ, c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      shortSum P.Q F x y ≤ C P.badDiscriminant * mainTerm P F x y := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hσ : 0 < ε * δ / 3 := by positivity
  have hσsmall : (g : ℝ) ^ 2 * (ε * δ / 3) ≤ 1 / 8 := by
    have H : ε * δ / 3 ≤ ε := by nlinarith
    exact (mul_le_mul_of_nonneg_left H (sq_nonneg _)).trans hsmall
  let c : ℝ := (g : ℝ) + 1 / δ + 1 / 8
  obtain ⟨x₀, hx₀, C, hC, H⟩ := exists_integerSum_mainTerm_bound hg hA hB hε hsmall
    hσ hσsmall (show 0 ≤ c by dsimp [c]; positivity)
    (primeArgument_growth_margin hg hε.le hδ hδ₁)
  obtain ⟨c₀, hc₀, Hinterval⟩ := exists_height_interval_threshold g hδ
    (show 0 < 4 * (g : ℝ) ^ 2 * ε by positivity) x₀
  refine ⟨c₀, hc₀, C, hC, ?_⟩
  intro k r P hdeg F hF x y hx hy hyx
  obtain ⟨hxx, hab, hlen, hlen', hvalue⟩ :=
    Hinterval P.total P.total_ne_zero hdeg x y hx hy hyx
  rw [P.shortSum_eq_integerSum F x y]
  exact H k r P hdeg F hF x y _ _ hxx hy hab hlen hlen' hvalue

/-- Theorem 1, equation (18), with the quantifier order recorded in `Targets`.
This is a proof of the original target proposition, not an additional hypothesis. -/
theorem theoremOne : TheoremOne := by
  intro k r g _ _ hg A B ε δ hA hB hε hsmall hδ hδ₁
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_shortSum_mainTerm_bound hg hA hB hε hsmall' hδ hδ₁
  exact ⟨c₀, hc₀, C, hC, H k r⟩

end NairTenenbaum
