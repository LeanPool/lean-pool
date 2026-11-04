/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Subpolynomial bounds for products over distinct prime factors -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

/-- A fixed exponential in the number of distinct prime factors is smaller
than every positive power of the integer, up to a uniform constant. -/
theorem exists_primeFactorPower_le_rpow {K η : ℝ} (hK : 1 ≤ K) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → K ^ n.primeFactors.card ≤ C * (n : ℝ) ^ η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (K ^ η⁻¹)
  refine ⟨K ^ (N + 1), one_le_pow₀ hK, ?_⟩
  intro n hn
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      K ≤ (if p ≤ N then K else 1) * (p : ℝ) ^ η := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    split_ifs with h
    · have H : 1 ≤ (p : ℝ) ^ η := Real.one_le_rpow (by exact_mod_cast hpprime.one_le) hη.le
      nlinarith
    · rw [one_mul]
      apply (Real.rpow_inv_le_iff_of_pos (zero_le_one.trans hK) (Nat.cast_nonneg p) hη).mp
      exact hN.le.trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h)))
  have hsmall : (∏ p ∈ n.primeFactors, if p ≤ N then K else 1) ≤ K ^ (N + 1) := by
    have hcard : (n.primeFactors.filter (· ≤ N)).card ≤ N + 1 := by
      apply le_trans (Finset.card_le_card (t := Finset.range (N + 1)) ?_) (by simp)
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hK hcard
  have hrad : (∏ p ∈ n.primeFactors, (p : ℝ) ^ η) ≤ (n : ℝ) ^ η := by
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) η]
    apply Real.rpow_le_rpow (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) _ hη.le
    have H := (Nat.cast_le (α := ℝ)).mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
        (Nat.prod_primeFactors_dvd n))
    simpa only [Nat.cast_prod] using H
  calc
    _ = ∏ _p ∈ n.primeFactors, K := (Finset.prod_const K).symm
    _ ≤ ∏ p ∈ n.primeFactors, (if p ≤ N then K else 1) * (p : ℝ) ^ η :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one.trans hK) hlocal
    _ = (∏ p ∈ n.primeFactors, if p ≤ N then K else 1) *
        ∏ p ∈ n.primeFactors, (p : ℝ) ^ η := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul hsmall hrad (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg
        (Nat.cast_nonneg _) _))
      (pow_nonneg (zero_le_one.trans hK) _)

theorem primeFactorPower_lcm_le {K : ℝ} (hK : 1 ≤ K) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    K ^ (Nat.lcm a b).primeFactors.card ≤ K ^ a.primeFactors.card * K ^ b.primeFactors.card := by
  have H := Finset.card_le_card (Nat.primeFactors_mono (Nat.lcm_dvd_mul a b) (mul_ne_zero ha hb))
  rw [Nat.primeFactors_mul ha hb] at H
  rw [← pow_add]
  exact pow_le_pow_right₀ hK (H.trans (Finset.card_union_le _ _))

end NairTenenbaum
