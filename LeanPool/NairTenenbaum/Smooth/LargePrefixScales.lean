/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.SieveScales

/-! # A uniform sieve level for large prefixes

Reducing the prime cutoff to `x^(g*ε/16)` leaves room to sieve all prefixes
of weighted mass at most `x^(3*g²*ε)`. Every smaller prime cutoff shares the
same lower threshold on `x`.
-/

@[expose] public section

namespace NairTenenbaum

theorem largePrefix_scale_exponent {g : ℕ} (hg : 0 < g) (ε : ℝ) (hε : 0 ≤ ε) :
    3 * (g : ℝ) ^ 2 * ε + (g : ℝ) * ε / 16 *
      (4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) + (g : ℝ) ^ 2 * ε / 2 ≤
        4 * (g : ℝ) ^ 2 * ε := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  nlinarith [mul_nonneg hε (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
    (sub_nonneg.mpr hg₁)), mul_nonneg (sq_nonneg (g : ℝ)) hε]

/-- A single height threshold supplies the conditional sieve level throughout
the large-prefix prime bands. The logarithmic lower bound on an individual
band cutoff is separate from this upper-cutoff estimate. -/
theorem exists_largePrefix_sieve_scales {g : ℕ} (hg : 0 < g) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ N y z : ℝ, 0 ≤ N → N ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → 0 ≤ z → z ≤ x ^ ((g : ℝ) * ε / 16) →
        L * N * z ^ (4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) ≤ y / 2 := by
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨x₀, hx₀, H⟩ := exists_sieve_scale_threshold
    (m := 3 * (g : ℝ) ^ 2 * ε) (d := 4 * (g : ℝ) ^ 2 * ε)
    (p := 4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) hL
    (show 0 < (g : ℝ) * ε / 16 by positivity)
    (show 0 < (g : ℝ) ^ 2 * ε / 2 by positivity)
    (by positivity) (by linarith [largePrefix_scale_exponent hg ε hε.le])
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  exact (H x hx).2.2

/-- The original sifted divisor sum at the large-prefix scale. -/
theorem exists_largePrefixSiftedSum_at_scales {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 1 ≤ K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (A B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 0 ≤ A → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a →
      P.smallDivisorSiftedSum F N a b (x ^ ((g : ℝ) * ε / 16)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * ((b : ℝ) - a) *
          sieveProduct P.total (x ^ ((g : ℝ) * ε / 16)) *
          ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_smallDivisorSiftedSum_bound hg
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨x₁, hx₁, hscale⟩ := exists_largePrefix_sieve_scales hg hε hL
  let α : ℝ := (g : ℝ) * ε / 16
  have hα : 0 < α := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    dsimp [α]
    positivity
  refine ⟨K, max x₁ (Real.exp (16 / α)), hK, hx₁.trans (le_max_left _ _), ?_⟩
  intro k r P hdeg A B σ F hF hA hB hσ hsmall x y N a b hxx hN hy hab hlength
  have hx₁' : x₁ ≤ x := (le_max_left _ _).trans hxx
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one (hx₁.trans hx₁')
  have hlog : 16 ≤ Real.log (x ^ α) := by
    have H' : 16 / α ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (16 / α))
        ((le_max_right _ _).trans hxx)
    rw [Real.log_rpow hx₀]
    nlinarith [(div_le_iff₀ hα).mp H']
  have hz : 2 ≤ x ^ α := by
    have H' := Real.add_one_le_exp (Real.log (x ^ α))
    rw [Real.exp_log (Real.rpow_pos_of_pos hx₀ _)] at H'
    linarith
  exact H k r P hdeg A B σ F hF hA hB hσ hsmall N a b _ hab hz hlog
    ((hscale x hx₁' N y (x ^ α) (by
      positivity) hN hy (Real.rpow_nonneg hx₀.le _) le_rfl).trans hlength)

end NairTenenbaum
