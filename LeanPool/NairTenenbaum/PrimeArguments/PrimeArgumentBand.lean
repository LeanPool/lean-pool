/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentMainTerm
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentTailSieve
public import LeanPool.NairTenenbaum.Smooth.PrimeBandDecay

/-! # A logarithmic prime band with the additional prime-argument saving -/

@[expose] public section

namespace NairTenenbaum

theorem primeArgument_band_decay {A c κ τ α x : ℝ} {g : ℕ}
    (hA : 0 < A) (hα : 0 < α) (hx : 1 < x)
    (hκ : c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2 ≤ κ * τ / 2) :
    A ^ (c / α) * Real.exp (4 * (g : ℝ) * Real.log 4 / α) *
        Real.exp (-κ * Real.log (x ^ τ) / Real.log (x ^ (2 * α))) / α ≤
      Real.exp (-1 / α) := by
  have HD := primeBand_decay_of_margin hA hα hx hκ
  calc
    _ ≤ Real.exp (-2 / α) / α := div_le_div_of_nonneg_right HD hα.le
    _ = Real.exp (-2 / α) * (1 / α) := by ring
    _ ≤ Real.exp (-2 / α) * Real.exp (1 / α) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 / α)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform sieve and moment estimate for one logarithmic prime band.
The moment strength pays the rough-remainder and Euler-product costs. Neither
the constant nor the lower threshold depends on the band's exponent `α`. -/
theorem exists_primeArgumentBandSiftedSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (A B σ κ c : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ A → 1 ≤ B → 0 < σ → 0 ≤ κ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 →
      ∀ (x y α : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x → 1 < x → 1 ≤ Real.log x →
      0 < α → 2 * α ≤ 1 → α ≤ (g : ℝ) * ε / 16 →
      2 ≤ x ^ α → 2 * (g : ℝ) ≤ x ^ α → 16 ≤ Real.log (x ^ α) →
      8 * (g : ℝ) ^ 2 * κ ≤ Real.log (x ^ (2 * α)) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      A ^ (c / α) * P.primeSmoothTailSiftedSum F g N (Finset.Icc 0 ⌊x ^ (2 * α)⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ α) ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * Real.exp (-1 / α) *
            primeMainTerm P F x y := by
  obtain ⟨K, L, hK, hL, H⟩ := exists_primeSmoothTailSiftedSum_bound hg
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨x₀, hx₀, hscale⟩ := exists_primeArgument_variable_sieve_scales hg hε hL
  refine ⟨2 * K, x₀, by linarith, hx₀, ?_⟩
  intro k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
    x y α N a b hxx hx hlog hα hα₁ hαcut hz hgz hzlog hwlog hN hy hab hlen hlen'
  have hx₀' : 0 < x := by linarith
  have hz₀ : 0 ≤ x ^ α := Real.rpow_nonneg hx₀'.le _
  have hw : 2 ≤ x ^ (2 * α) := hz.trans
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hwx : x ^ (2 * α) ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le hα₁
  have hlevel := (hscale x hxx N y (x ^ α) (by positivity) hN hy hz₀
    (Real.rpow_le_rpow_of_exponent_le hx.le hαcut)).trans hlen
  have HS := H k r P hdeg hzero A B σ κ F hF (by linarith) hB hσ hκ hσsmall
    (x ^ (2 * α)) (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) hw hwlog
    (Real.rpow_pos_of_pos hx₀' _) N a b (x ^ α) hab hz hzlog hlevel
  have HE := sieveProduct_power_cutoff_le P.noFixedPrime hdeg.le hα (by linarith) hx.le hlog hz hgz
  change sieveProduct P.total (x ^ α) ≤
    Real.exp (4 * (g : ℝ) * Real.log 4 / α) * sieveProduct P.total x at HE
  have HD := primeArgument_band_decay (by linarith : 0 < A) hα hx hdecay
  have hprod : A ^ (c / α) * sieveProduct P.total (x ^ α) *
      Real.exp (-κ * Real.log (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) / Real.log (x ^ (2 * α))) / α ≤
      Real.exp (-1 / α) * sieveProduct P.total x := by
    have H₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left HE (Real.rpow_nonneg (by linarith : 0 ≤ A) (c / α)))
      (Real.exp_nonneg (-κ * Real.log (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) / Real.log (x ^ (2 * α))))
    have H₁div := div_le_div_of_nonneg_right H₁ hα.le
    have H₂ := mul_le_mul_of_nonneg_right HD (sieveProduct_pos P.noFixedPrime x).le
    apply H₁div.trans
    convert H₂ using 1 <;> simp only [PolynomialSystem.total]
    ring
  have hsum : (∑ n ∈ positiveUpTo (x ^ (2 * α)), P.weight F n) ≤
      ∑ n ∈ positiveUpTo x, P.weight F n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact (mem_positiveUpTo n x).mpr (((mem_positiveUpTo n _).mp hn).trans hwx)
    · intro n _ _
      exact P.weight_nonneg hF.nonneg n
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₀'.le _).trans hy
  have hs₀ : 0 ≤ ∑ n ∈ positiveUpTo (x ^ (2 * α)), P.weight F n :=
    Finset.sum_nonneg (fun n _ => P.weight_nonneg hF.nonneg n)
  have hp₀ : 0 ≤ A ^ (c / α) * sieveProduct P.total (x ^ α) *
      Real.exp (-κ * Real.log (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) / Real.log (x ^ (2 * α))) / α :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by
      linarith) _) (sieveProduct_pos P.noFixedPrime _).le)
      (Real.exp_nonneg _)) hα.le
  have H₁ := mul_le_mul hlen' hprod hp₀ (by positivity : 0 ≤ 2 * y)
  have H₂ := mul_le_mul H₁ hsum hs₀
    (mul_nonneg (by
      positivity) (mul_nonneg (Real.exp_nonneg _) (sieveProduct_pos P.noFixedPrime x).le))
  have hcost := (primeArgumentTailSieveCost_pos (A := A) (κ := κ) (lt_of_lt_of_le zero_lt_one hB)
      hg P.badDiscriminant_pos).le
  have H₃ := mul_le_mul_of_nonneg_left H₂ (mul_nonneg (zero_le_one.trans hK) hcost)
  apply (mul_le_mul_of_nonneg_left HS (Real.rpow_nonneg (by linarith : 0 ≤ A) (c / α))).trans
  have H₄ := mul_le_mul_of_nonneg_right H₃
    (primeArgumentFactor_nonneg P.total (z := x) hx.le)
  rw [primeArgumentFactor_rpow P.total hx₀']
  dsimp only [primeMainTerm, mainTerm]
  convert H₄ using 1 <;> ring

end NairTenenbaum
