/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.PrimeBandSummation

/-! # A fixed lower cutoff for all large-prefix bands -/

@[expose] public section

namespace NairTenenbaum

/-- A fixed cutoff on the upper edge of a band supplies every lower-cutoff
condition in the sieve and moment estimates. It is independent of coefficients,
discriminants, and the band index. -/
theorem exists_primeBand_lower_cutoff {g : ℕ} (hg : 0 < g) (κ : ℝ) :
    ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ (x α : ℝ), 0 < x → w₀ ≤ x ^ (2 * α) →
      2 ≤ x ^ α ∧ 2 * (g : ℝ) ≤ x ^ α ∧ 16 ≤ Real.log (x ^ α) ∧
        8 * (g : ℝ) ^ 2 * κ ≤ Real.log (x ^ (2 * α)) := by
  let M : ℝ := max 32 (max (2 * Real.log (2 * (g : ℝ))) (8 * (g : ℝ) ^ 2 * κ))
  have hM : 32 ≤ M := le_max_left _ _
  refine ⟨Real.exp M, Real.one_lt_exp_iff.mpr (by linarith), ?_⟩
  intro x α hx hw
  have H : M ≤ Real.log (x ^ (2 * α)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos M) hw
  have heq : Real.log (x ^ (2 * α)) = 2 * Real.log (x ^ α) := by
    rw [Real.log_rpow hx, Real.log_rpow hx]
    ring
  have hzlog : 16 ≤ Real.log (x ^ α) := by rw [heq] at H; linarith
  have hz : 2 ≤ x ^ α := by
    have H' := Real.add_one_le_exp (Real.log (x ^ α))
    rw [Real.exp_log (Real.rpow_pos_of_pos hx _)] at H'
    linarith
  have hgz : 2 * (g : ℝ) ≤ x ^ α := by
    have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
    apply (Real.log_le_log_iff (by positivity : 0 < 2 * (g : ℝ)) (Real.rpow_pos_of_pos hx _)).mp
    have H' : 2 * Real.log (2 * (g : ℝ)) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    rw [heq] at H
    linarith
  exact ⟨hz, hgz, hzlog, ((le_max_right _ _).trans (le_max_right _ _)).trans H⟩

/-- A moment strength with strictly positive decay margin always exists for
the nonnegative polynomial-value exponent used in the main proof. -/
theorem exists_primeBand_moment {g : ℕ} (hg : 0 < g) {ε A c : ℝ}
    (hε : 0 < ε) (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ κ : ℝ, 0 < κ ∧
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 1 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 := by
  let v := c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 1
  have hv : 0 < v := by
    dsimp only [v]
    have h₁ := mul_nonneg hc (Real.log_nonneg hA)
    have h₂ := mul_nonneg (show (0 : ℝ) ≤ 4 * g by
      positivity) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    linarith
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have ht : 0 < 3 * (g : ℝ) ^ 2 * ε / 2 := by positivity
  refine ⟨2 * v / (3 * (g : ℝ) ^ 2 * ε / 2), by positivity, ?_⟩
  rw [div_mul_cancel₀ _ ht.ne']
  dsimp only [v]
  linarith

/-- All bands above a single fixed smoothness cutoff satisfy the summed
main-term bound. The moment and cutoff are chosen before the polynomials. -/
theorem exists_largePrefixBands_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε A c : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ (x y u : ℝ) (N : ℕ+) (a b : ℤ) (J : Finset ℕ),
      x₀ ≤ x → 1 < x → 1 ≤ Real.log x → 0 < u → u ≤ 1 → u ≤ (g : ℝ) * ε / 16 →
      (∀ j ∈ J, w₀ ≤ x ^ (2 * (u / 2 ^ (j + 1)))) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      (∑ j ∈ J, P.smoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1)))) ≤
        K * smoothTailSieveCost A B κ g P.badDiscriminant * mainTerm P F x y := by
  obtain ⟨K, x₀, hK, hx₀, H⟩ := exists_primeBandSum_mainTerm_bound hg hε
  obtain ⟨κ, hκ, hmoment⟩ := exists_primeBand_moment hg hε hA hc
  obtain ⟨w₀, hw₀, hcut⟩ := exists_primeBand_lower_cutoff hg κ
  refine ⟨K, x₀, κ, w₀, hK, hx₀, hκ, hw₀, ?_⟩
  intro k r P hdeg B σ F hF hB hσ hσsmall x y u N a b J
    hxx hx hlog hu hu₁ hucut hJ hN hy hab hlen hlen' hvalue
  exact H k r P hdeg A B σ κ c F hF hA hB hσ hκ.le hσsmall hmoment
    x y u N a b J hxx hx hlog hu hu₁ hucut
    (fun j hj => hcut x (u / 2 ^ (j + 1)) (by linarith) (hJ j hj))
    hN hy hab hlen hlen' hvalue

end NairTenenbaum
