/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.SievePrimes

/-! # A uniform subpolynomial lower bound for the sifting product -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem sieveFactor_inv_le_prime {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {p : ℕ} (hp : p.Prime) : (1 - (rootCount Q p : ℝ) / p)⁻¹ ≤ p := by
  simpa only [omittedEulerRatio, pow_zero, one_div] using omittedEulerRatio_le_prime hQ 0 hp

theorem sieveFactor_inv_le_exp {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g p : ℕ} (hg : Q.natDegree ≤ g) (hp : p.Prime) (hlarge : 2 * g ≤ p) :
    (1 - (rootCount Q p : ℝ) / p)⁻¹ ≤ Real.exp (2 * (g : ℝ) / p) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr : (rootCount Q p : ℝ) / p ≤ (g : ℝ) / p :=
    div_le_div_of_nonneg_right (by exact_mod_cast (rootCount_le_degree hQ hp).trans hg) hp₀.le
  have hhalf : (g : ℝ) / p ≤ 1 / 2 := (div_le_iff₀ hp₀).mpr (by
    have H : 2 * (g : ℝ) ≤ p := by exact_mod_cast hlarge
    linarith)
  have ht : 0 ≤ (rootCount Q p : ℝ) / p := by positivity
  have hden : 0 < 1 - (rootCount Q p : ℝ) / p := by linarith
  have H : (1 - (rootCount Q p : ℝ) / p)⁻¹ ≤ 1 + 2 * ((rootCount Q p : ℝ) / p) := by
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr (hr.trans hhalf))]
  calc
    _ ≤ _ := H
    _ ≤ 1 + 2 * (g : ℝ) / p := by rw [mul_div_assoc]; linarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (2 * (g : ℝ) / p)

/-- Uniformly in the polynomial coefficients, the inverse sifting product is
smaller than every positive power of its cutoff, up to a degree-dependent constant. -/
theorem exists_sieveProduct_inv_le_rpow (g : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : ℤ[X]), NoFixedPrimeDivisor Q → Q.natDegree ≤ g →
      ∀ z : ℝ, 2 ≤ z → (sieveProduct Q z)⁻¹ ≤ C * z ^ δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (g : ℝ) + 2) (Real.exp (2 * (g : ℝ) * Real.log 4 / δ)))
  have hNbig : 2 * (g : ℝ) + 2 < N := (le_max_left _ _).trans_lt hN
  have hNexp : Real.exp (2 * (g : ℝ) * Real.log 4 / δ) < N := (le_max_right _ _).trans_lt hN
  have hN₂ : (2 : ℝ) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) g]
  have hN₁ : (1 : ℝ) ≤ N := by linarith
  have hNg : 2 * g ≤ N := by exact_mod_cast (show 2 * (g : ℝ) ≤ N by linarith)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hcoef : 2 * (g : ℝ) * Real.log 4 / Real.log N ≤ δ := by
    apply (div_le_iff₀ hlogN).mpr
    have H := Real.log_le_log (Real.exp_pos _) hNexp.le
    rw [Real.log_exp] at H
    have H' := (div_le_iff₀ hδ).mp H
    linarith
  let C : ℝ := (N : ℝ) ^ (N + 1) * Real.exp δ
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN₁) (Real.one_le_exp_iff.mpr
      hδ.le)
  refine ⟨C, hC, ?_⟩
  intro Q hQ hg z hz
  let S := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime
  let u : ℕ → ℝ := fun p => if N < p then 2 * (g : ℝ) / p else 0
  have hf (p : ℕ) (hp : p ∈ S) :
      (1 - (rootCount Q p : ℝ) / p)⁻¹ ≤ (if p ≤ N then (N : ℝ) else 1) * Real.exp (u p) := by
    have hprime := (Finset.mem_filter.mp hp).2
    by_cases h : p ≤ N
    · simp only [ite_eq_left h, u, ite_eq_right (Nat.not_lt.mpr h), Real.exp_zero, mul_one]
      exact (sieveFactor_inv_le_prime hQ hprime).trans (by exact_mod_cast h)
    · simp only [ite_eq_right h, u, ite_eq_left (Nat.lt_of_not_ge h), one_mul]
      exact sieveFactor_inv_le_exp hQ hg hprime (hNg.trans (Nat.le_of_lt (Nat.lt_of_not_ge h)))
  have hsmall : (∏ p ∈ S, if p ≤ N then (N : ℝ) else 1) ≤ (N : ℝ) ^ (N + 1) := by
    have hcard : (S.filter (· ≤ N)).card ≤ N + 1 := by
      apply le_trans (Finset.card_le_card (t := Finset.range (N + 1)) ?_) (by simp)
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hN₁ hcard
  have hsum : (∑ p ∈ S, u p) ≤ δ * (1 + Real.log z) := by
    have hset : S.filter (fun p => N < p) = (primeBandNumbers (N : ℝ) z).filter Nat.Prime := by
      ext p
      simp [S, primeBandNumbers, _root_.and_comm, _root_.and_left_comm]
    calc
      _ = 2 * (g : ℝ) * ∑ p ∈ (primeBandNumbers (N : ℝ) z).filter Nat.Prime, (p : ℝ)⁻¹ := by
        dsimp only [u]
        rw [← Finset.sum_filter, hset, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (g : ℝ) * (Real.log 4 * (1 + Real.log z) / Real.log N) :=
        mul_le_mul_of_nonneg_left (primeBand_reciprocal_sum_le hN₂ hz) (by positivity)
      _ = (2 * (g : ℝ) * Real.log 4 / Real.log N) * (1 + Real.log z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by
        have H := Real.log_nonneg (by linarith : 1 ≤ z); linarith)
  calc
    _ = ∏ p ∈ S, (1 - (rootCount Q p : ℝ) / p)⁻¹ := by rw [sieveProduct, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ S, (if p ≤ N then (N : ℝ) else 1) * Real.exp (u p) := by
      apply Finset.prod_le_prod₀ _ hf
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      exact (inv_pos.mpr (sub_pos.mpr ((div_lt_one (by
        exact_mod_cast hprime.pos)).mpr (by exact_mod_cast hQ p hprime)))).le
    _ = (∏ p ∈ S, if p ≤ N then (N : ℝ) else 1) * Real.exp (∑ p ∈ S, u p) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    _ ≤ (N : ℝ) ^ (N + 1) * Real.exp (δ * (1 + Real.log z)) :=
      mul_le_mul hsmall (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _) (pow_nonneg
          (Nat.cast_nonneg _) _)
    _ = C * z ^ δ := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < z)]
      dsimp [C]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end NairTenenbaum
