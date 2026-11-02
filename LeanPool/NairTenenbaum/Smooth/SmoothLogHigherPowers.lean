/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SmoothLogCountingError
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Bounded higher-prime-power contributions to the logarithmic main term -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem sum_inverse_prime_powers_ge_two_le {p : ℝ} (hp : 2 ≤ p) (L : ℕ) :
    (∑ ν ∈ Icc 2 L, p⁻¹ ^ ν) ≤ 2 / p ^ 2 := by
  have hp₀ : 0 < p := by linarith
  have hi : 0 ≤ p⁻¹ := inv_nonneg.mpr hp₀.le
  have hh : p⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hi₁ : p⁻¹ < 1 := by linarith
  have HE : Icc 2 L = Ico 2 (L + 1) := by ext i; simp only [mem_Icc, mem_Ico]; omega
  rw [HE]
  apply (geom_sum_Ico_le_of_lt_one hi hi₁).trans
  have H : p⁻¹ ^ 2 / (1 - p⁻¹) ≤ 2 * p⁻¹ ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - p⁻¹)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg p⁻¹)]
  simpa only [inv_pow, div_eq_mul_inv] using H

theorem local_smoothLogRootMain_le {Q : ℤ[X]} {p L : ℕ} (hp : p.Prime) {K : ℝ}
    (hK : 0 ≤ K) (hroot : ∀ ν : ℕ, 0 < ν → (rootCount Q (p ^ ν) : ℝ) ≤ K) :
    (∑ ν ∈ Icc 1 L, (rootCount Q (p ^ ν) : ℝ) / (p : ℝ) ^ ν) ≤
      (rootCount Q p : ℝ) / p + 2 * K / (p : ℝ) ^ 2 := by
  classical
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  by_cases hL : L = 0
  · subst L
    simp only [Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), sum_empty]
    positivity
  · have HE : Icc 1 L = insert 1 (Icc 2 L) := by ext i; simp only [mem_Icc, mem_insert]; omega
    rw [HE, sum_insert (by simp), pow_one, pow_one]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ ν ∈ Icc 2 L, K * (p : ℝ)⁻¹ ^ ν := by
        apply sum_le_sum
        intro ν hν
        have H := div_le_div_of_nonneg_right (hroot ν (by have := (mem_Icc.mp hν).1; omega))
          (pow_nonneg hp₀.le ν)
        simpa only [div_eq_mul_inv, inv_pow] using H
      _ = K * ∑ ν ∈ Icc 2 L, (p : ℝ)⁻¹ ^ ν := by rw [mul_sum]
      _ ≤ K * (2 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left
        (sum_inverse_prime_powers_ge_two_le (by exact_mod_cast hp.two_le) L) hK
      _ = _ := by ring

theorem summable_log_div_nat_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
  have HS : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
  apply Summable.of_nonneg_of_le _ _ HS
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) (sq_nonneg _)
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hn₀ : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have H := div_le_div_of_nonneg_right (Real.log_le_rpow_div hn₀.le (by
        norm_num : (0 : ℝ) < 1 / 2)) (sq_nonneg (n : ℝ))
      have HE : ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / (n : ℝ) ^ 2 = 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        calc
          _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (2 : ℝ)) := by rw [Real.rpow_ofNat]; ring
          _ = 2 * (n : ℝ) ^ ((1 / 2 : ℝ) - 2) := by rw [← Real.rpow_sub hn₀]
          _ = _ := by norm_num
      exact H.trans_eq HE

/-- The prime sum weighted by root counts and logarithms. -/
noncomputable def primeRootLogSum (Q : ℤ[X]) (z : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (rootCount Q p : ℝ) / p * Real.log p

theorem exists_smoothLogRootMain_le_prime_sum {Q : ℤ[X]} (hQ : Q.IsPrimitive) (hD : Q.discr ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℝ) (L : ℕ → ℕ), smoothLogRootMain Q z L ≤ primeRootLogSum Q z + B := by
  let K : ℝ := (max Q.natDegree (Q.discr.natAbs ^ 3) : ℕ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let T : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2
  have hterm (n : ℕ) : 0 ≤ Real.log n / (n : ℝ) ^ 2 := by
    by_cases hn : n = 0
    · simp [hn]
    · exact div_nonneg (Real.log_nonneg (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) (sq_nonneg _)
  have hT : 0 ≤ T := tsum_nonneg hterm
  refine ⟨2 * K * T, by positivity, fun z L => ?_⟩
  have HS := summable_log_div_nat_sq.sum_le_tsum ((range (⌊z⌋₊ + 1)).filter Nat.Prime) (fun n _ =>
      hterm n)
  unfold smoothLogRootMain primeRootLogSum
  calc
    _ ≤ ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        ((rootCount Q p : ℝ) / p + 2 * K / (p : ℝ) ^ 2) * Real.log p := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).2
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le))
      exact local_smoothLogRootMain_le hp' hK (fun ν _ => by
        dsimp [K]
        exact_mod_cast primitive_rootCount_prime_pow_uniform hQ hD hp' ν)
    _ = (∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (rootCount Q p : ℝ) / p * Real.log p) +
        2 * K * (∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, Real.log p / (p : ℝ) ^ 2) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left HS (by positivity : 0 ≤ 2 * K))

end NairTenenbaum
