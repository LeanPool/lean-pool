/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.SmallDivisorSum

/-! # Sieve levels at the small-divisor scales of the main proof -/

@[expose] public section

namespace NairTenenbaum

/-- A positive exponent gap pays the fixed sieve constant uniformly in every
smaller cutoff. The same threshold supplies the logarithmic lower bound. -/
theorem exists_sieve_scale_threshold {L α m d p e : ℝ}
    (hL : 1 ≤ L) (hα : 0 < α) (he : 0 < e) (hp : 0 ≤ p)
    (hgap : e + m + α * p ≤ d) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 ≤ x ^ α ∧ 16 ≤ Real.log (x ^ α) ∧
      ∀ N y z : ℝ, 0 ≤ N → N ≤ x ^ m → x ^ d ≤ y → 0 ≤ z → z ≤ x ^ α →
        L * N * z ^ p ≤ y / 2 := by
  let t := max 0 (max (16 / α) (Real.log (2 * L) / e))
  have ⟨ht₀, htα, hte⟩ : 0 ≤ t ∧ 16 / α ≤ t ∧ Real.log (2 * L) / e ≤ t := by
    simp [t, le_max_iff]
  refine ⟨Real.exp t, Real.one_le_exp_iff.mpr ht₀, ?_⟩
  intro x hx
  have hx₁ : 1 ≤ x := (Real.one_le_exp_iff.mpr ht₀).trans hx
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx₁
  have ht : t ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hx
  have hlog : 16 ≤ Real.log (x ^ α) := by
    rw [Real.log_rpow hx₀]
    nlinarith [(div_le_iff₀ hα).mp (htα.trans ht)]
  have htwo : 2 ≤ x ^ α := by
    have H := Real.add_one_le_exp (Real.log (x ^ α))
    rw [Real.exp_log (Real.rpow_pos_of_pos hx₀ α)] at H
    linarith
  have hconstant : 2 * L ≤ x ^ e := by
    apply (Real.log_le_log_iff (by linarith : 0 < 2 * L)
      (Real.rpow_pos_of_pos hx₀ e)).mp
    rw [Real.log_rpow hx₀]
    nlinarith [(div_le_iff₀ he).mp (hte.trans ht)]
  refine ⟨htwo, hlog, ?_⟩
  intro N y z hN hNx hy hz hzx
  have Hz := Real.rpow_le_rpow hz hzx hp
  rw [← Real.rpow_mul hx₀.le] at Hz
  have H := mul_le_mul hconstant hNx hN (Real.rpow_nonneg hx₀.le e)
  have H' := mul_le_mul H Hz (Real.rpow_nonneg hz _) (by positivity)
  rw [← Real.rpow_add hx₀, ← Real.rpow_add hx₀] at H'
  have H'' := H'.trans ((Real.rpow_le_rpow_of_exponent_le hx₁ hgap).trans hy)
  nlinarith

/-- The small-divisor and prime cutoffs leave a positive exponent gap beneath
Theorem 1's lower bound on the interval length. -/
theorem smallDivisor_scale_exponent {g : ℕ} (hg : 0 < g) (ε : ℝ) (hε : 0 ≤ ε) :
    3 * (g : ℝ) ^ 2 * ε / 2 + (g : ℝ) * ε / 2 *
      (4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) + (g : ℝ) ^ 2 * ε / 4 ≤
        4 * (g : ℝ) ^ 2 * ε := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  nlinarith [mul_nonneg hε (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
    (sub_nonneg.mpr hg₁))]

/-- One uniform threshold makes the paper's two cutoffs satisfy the logarithmic
and size conditions of the conditional sieve, including a factor two for passing
to integer endpoints. -/
theorem exists_smallDivisor_sieve_scales {g : ℕ} (hg : 0 < g) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      2 ≤ x ^ ((g : ℝ) * ε / 2) ∧ 16 ≤ Real.log (x ^ ((g : ℝ) * ε / 2)) ∧
      ∀ N y : ℝ, 0 ≤ N → N ≤ x ^ (3 * (g : ℝ) ^ 2 * ε / 2) →
        x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
        L * N * (x ^ ((g : ℝ) * ε / 2)) ^
          (4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) ≤ y / 2 := by
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨x₀, hx₀, H⟩ := exists_sieve_scale_threshold
    (m := 3 * (g : ℝ) ^ 2 * ε / 2) (d := 4 * (g : ℝ) ^ 2 * ε)
    (p := 4 * (g : ℝ) * (1 + 1 / 16) + 1 / 4) hL
    (show 0 < (g : ℝ) * ε / 2 by positivity)
    (show 0 < (g : ℝ) ^ 2 * ε / 4 by positivity)
    (by positivity) (by linarith [smallDivisor_scale_exponent hg ε hε.le])
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx
  obtain ⟨hz, hlog, hlevel⟩ := H x hx
  refine ⟨hz, hlog, ?_⟩
  intro N y hN hNx hy
  exact hlevel N y _ hN hNx hy (by positivity) le_rfl

/-- The small-divisor sum at the paper's scales, with constants chosen before
all polynomial coefficients and the admissible arithmetic function. -/
theorem exists_smallDivisorSiftedSum_at_scales {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 1 ≤ K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → ∀ (A B σ : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 0 ≤ A → 1 ≤ B → 0 < σ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε / 2) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a →
      P.smallDivisorSiftedSum F N a b (x ^ ((g : ℝ) * ε / 2)) ≤
        K * smallDivisorSieveCost B σ g P.badDiscriminant * ((b : ℝ) - a) *
          sieveProduct P.total (x ^ ((g : ℝ) * ε / 2)) *
          ∑ n ∈ Finset.Icc 1 N, P.weight F n := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_smallDivisorSiftedSum_bound hg
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨x₀, hx₀, hx⟩ := exists_smallDivisor_sieve_scales hg hε hL
  refine ⟨K, x₀, hK, hx₀, ?_⟩
  intro k r P hdeg A B σ F hF hA hB hσ hsmall x y N a b hxx hN hy hab hlength
  obtain ⟨hz, hzlog, hlevel⟩ := hx x hxx
  exact H k r P hdeg A B σ F hF hA hB hσ hsmall N a b _ hab hz hzlog
    ((hlevel N y (by positivity) hN hy).trans hlength)

end NairTenenbaum
