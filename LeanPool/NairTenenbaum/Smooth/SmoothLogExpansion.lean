/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.ScalarPrimeSplit

/-! # Exact logarithmic expansion of the smooth part -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem log_nat_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  have H : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hn
  have HE : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast H.symm
  rw [HE, Real.log_prod]
  · apply sum_congr rfl
    intro p _
    exact Real.log_pow p _
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem log_smoothPart_eq_prime_sum (n : ℕ+) {z : ℝ} (hz : 0 ≤ z) :
    Real.log (smoothPart n z : ℕ) =
      ∑ p ∈ (n : ℕ).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ z),
        ((n : ℕ).factorization p : ℝ) * Real.log p := by
  rw [log_nat_eq_sum_factorization (smoothPart n z).ne_zero]
  change (∑ p ∈ (primeSelect (fun _ : Fin 1 => n) (range (⌊z⌋₊ + 1)) 0 : ℕ).primeFactors,
    (((primeSelect (fun _ : Fin 1 => n) (range (⌊z⌋₊ + 1)) 0 : ℕ).factorization p) : ℝ) * Real.log
        p) = _
  rw [primeFactors_primeSelect]
  have HE : (n : ℕ).primeFactors ∩ range (⌊z⌋₊ + 1) =
      (n : ℕ).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ z) := by
    ext p
    simp only [mem_inter, mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hz, mem_filter]
  rw [HE]
  apply sum_congr rfl
  intro p hp
  rw [factorization_primeSelect]
  have hmem : p ∈ range (⌊z⌋₊ + 1) := mem_range.mpr (Nat.lt_succ_iff.mpr
    ((Nat.le_floor_iff hz).mpr (mem_filter.mp hp).2))
  rw [ite_eq_left hmem]

/-- A fixed common prime cutoff allows summing the local logarithmic masses
before estimating how often each prime power divides a value. -/
theorem sum_log_smoothPart_eq_prime_sum {ι : Type*} (S : Finset ι) (n : ι → ℕ+)
    {z : ℝ} (hz : 0 ≤ z) :
    (∑ i ∈ S, Real.log (smoothPart (n i) z : ℕ)) =
      ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        (∑ i ∈ S, ((n i : ℕ).factorization p : ℝ)) * Real.log p := by
  classical
  have H (i : ι) : Real.log (smoothPart (n i) z : ℕ) =
      ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime,
        ((n i : ℕ).factorization p : ℝ) * Real.log p := by
    rw [log_smoothPart_eq_prime_sum (n i) hz]
    apply sum_subset
    · intro p hp
      obtain ⟨hp, hpz⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr ((Nat.le_floor_iff hz).mpr hpz)),
        Nat.prime_of_mem_primeFactors hp⟩
    · intro p hp hnot
      have hpz : (p : ℝ) ≤ z := (Nat.le_floor_iff hz).mp
        (Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1))
      have hn : p ∉ (n i : ℕ).primeFactors := by intro h; exact hnot (mem_filter.mpr ⟨h, hpz⟩)
      have Hzero : (n i : ℕ).factorization p = 0 := by
        simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hn
      simp only [Hzero, Nat.cast_zero, zero_mul]
  simp_rw [H]
  rw [sum_comm]
  simp only [sum_mul]

end NairTenenbaum
