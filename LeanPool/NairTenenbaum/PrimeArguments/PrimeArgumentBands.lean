/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentBandContribution
public import LeanPool.NairTenenbaum.Smooth.PrimeBandCutoff

/-! # Summing logarithmic prefix bands at prime arguments

The moment strength pays the extra reciprocal band exponent. The resulting
geometric majorant and lower smoothness cutoff are uniform in the polynomial
coefficients and in the number of bands.
-/

@[expose] public section

namespace NairTenenbaum

/-- The sum of the original weighted contributions over any finite collection
of eligible bands is bounded uniformly in the number of bands. -/
theorem exists_primeArgumentBandSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (A B σ κ c : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ A → 1 ≤ B → 0 < σ → 0 ≤ κ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 →
      ∀ (x y u : ℝ) (N : ℕ+) (a b : ℤ) (J : Finset ℕ), x₀ ≤ x → 1 < x → 1 ≤ Real.log x →
      0 < u → u ≤ 1 → u ≤ (g : ℝ) * ε / 16 →
      (∀ j ∈ J, 2 ≤ x ^ (u / 2 ^ (j + 1)) ∧ 2 * (g : ℝ) ≤ x ^ (u / 2 ^ (j + 1)) ∧
        16 ≤ Real.log (x ^ (u / 2 ^ (j + 1))) ∧
        8 * (g : ℝ) ^ 2 * κ ≤ Real.log (x ^ (2 * (u / 2 ^ (j + 1))))) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      (∑ j ∈ J, P.primeSmoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j +
          1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1)))) ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * primeMainTerm P F x y := by
  obtain ⟨K, x₀, hK, hx₀, H⟩ := exists_primeArgumentBandContribution_mainTerm_bound hg hε
  have hden : 0 < 1 - Real.exp (-1) := sub_pos.mpr (by
    rw [Real.exp_lt_one_iff]
    norm_num)
  refine ⟨K * (1 - Real.exp (-1))⁻¹, x₀, mul_pos hK (inv_pos.mpr hden), hx₀, ?_⟩
  intro k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
    x y u N a b J hxx hx hlog hu hu₁ hucut hJ hN hy hab hlen hlen' hvalue
  have hband (j : ℕ) (hj : j ∈ J) :
      P.primeSmoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1))) ≤
      K * primeArgumentTailSieveCost A B κ g P.badDiscriminant *
        Real.exp (-1 / (u / 2 ^ (j + 1))) * primeMainTerm P F x y := by
    have hα : 0 < u / 2 ^ (j + 1) := by positivity
    have hαu := dyadic_primeBand_exponent_le hu.le j
    obtain ⟨hz, hgz, hzlog, hwlog⟩ := hJ j hj
    exact H k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
      x y (u / 2 ^ (j + 1)) N a b hxx hx hlog hα (hαu.trans hu₁)
      ((by linarith : u / 2 ^ (j + 1) ≤ u).trans hucut)
      hz hgz hzlog hwlog hN hy hab hlen hlen' hvalue
  have hcost := (primeArgumentTailSieveCost_pos (A := A) (κ := κ)
    (lt_of_lt_of_le zero_lt_one hB) hg P.badDiscriminant_pos).le
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  have hm : 0 ≤ primeMainTerm P F x y := primeMainTerm_nonneg P hF.nonneg hx.le hy₀
  have Hsum := sum_le_dyadic_primeBand_bound hu hu₁ J
    (mul_nonneg (mul_nonneg hK.le hcost) hm) _ (fun j hj => by
      convert hband j hj using 1; ring)
  convert Hsum using 1; ring

/-- A moment strength with strictly positive decay margin always exists for
the nonnegative polynomial-value exponent used in the main proof. -/
theorem exists_primeArgumentBand_moment {g : ℕ} (hg : 0 < g) {ε A c : ℝ}
    (hε : 0 < ε) (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ κ : ℝ, 0 < κ ∧
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 := by
  let v := c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2
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
theorem exists_primeArgumentBands_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε A c : ℝ} (hε : 0 < ε) (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ (x y u : ℝ) (N : ℕ+) (a b : ℤ) (J : Finset ℕ),
      x₀ ≤ x → 1 < x → 1 ≤ Real.log x → 0 < u → u ≤ 1 → u ≤ (g : ℝ) * ε / 16 →
      (∀ j ∈ J, w₀ ≤ x ^ (2 * (u / 2 ^ (j + 1)))) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      (∑ j ∈ J, P.primeSmoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j +
          1)))⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ (u / 2 ^ (j + 1)))) ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * primeMainTerm P F x y := by
  obtain ⟨K, x₀, hK, hx₀, H⟩ := exists_primeArgumentBandSum_mainTerm_bound hg hε
  obtain ⟨κ, hκ, hmoment⟩ := exists_primeArgumentBand_moment hg hε hA hc
  obtain ⟨w₀, hw₀, hcut⟩ := exists_primeBand_lower_cutoff hg κ
  refine ⟨K, x₀, κ, w₀, hK, hx₀, hκ, hw₀, ?_⟩
  intro k r P hdeg hzero B σ F hF hB hσ hσsmall x y u N a b J
    hxx hx hlog hu hu₁ hucut hJ hN hy hab hlen hlen' hvalue
  exact H k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ.le hσsmall hmoment
    x y u N a b J hxx hx hlog hu hu₁ hucut
    (fun j hj => hcut x (u / 2 ^ (j + 1)) (by linarith) (hJ j hj))
    hN hy hab hlen hlen' hvalue

end NairTenenbaum
