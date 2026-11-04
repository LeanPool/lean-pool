/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.RoughCofactorBounds

/-! # Counting a saved prime factor in the total rough logarithmic mass -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem rough_logMass_le_saved_factors {ι : Type*} (S H : Finset ι) (hH : H ⊆ S)
    (b : ι → ℕ) (hb : ∀ i ∈ S, b i ≠ 0) {k : ℕ} (hk : 2 ≤ k) {P : ℝ} (hP : 1 ≤ P)
    (hprimes : ∀ i ∈ S, ∀ p ∈ (b i).primeFactors, (p : ℝ) ≤ P)
    (hΩ : ∀ i ∈ S, bigOmega (b i) ≤ k - 1)
    (hΩH : ∀ i ∈ H, bigOmega (b i) ≤ k - 2) :
    (∑ i ∈ S, Real.log (b i)) ≤ (((k : ℝ) - 1) * S.card - H.card) * Real.log P := by
  classical
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
  have Hbase (i : ι) (hi : i ∈ S) : Real.log (b i) ≤ ((k : ℝ) - 1) * Real.log P := by
    apply (log_le_bigOmega_mul_log (hb i hi) hP (hprimes i hi)).trans
    apply mul_le_mul_of_nonneg_right _ hlog
    have H : (bigOmega (b i) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hΩ i hi
    simpa only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] using H
  have Hsave (i : ι) (hi : i ∈ H) : Real.log (b i) ≤ ((k : ℝ) - 2) * Real.log P := by
    apply (log_le_bigOmega_mul_log (hb i (hH hi)) hP (hprimes i (hH hi))).trans
    apply mul_le_mul_of_nonneg_right _ hlog
    have H : (bigOmega (b i) : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast hΩH i hi
    simpa only [Nat.cast_sub hk, Nat.cast_ofNat] using H
  calc
    _ ≤ ∑ i ∈ S, (((k : ℝ) - 1) * Real.log P - if i ∈ H then Real.log P else 0) := by
      apply sum_le_sum
      intro i hi
      by_cases h : i ∈ H
      · rw [ite_eq_left h]
        convert Hsave i h using 1; ring
      · simpa only [ite_eq_right h, sub_zero] using Hbase i hi
    _ = _ := by
      rw [sum_sub_distrib, ← sum_filter]
      have HE : S.filter (fun i => i ∈ H) = H := by
        ext i; simp only [mem_filter]; exact ⟨And.right, fun h => ⟨hH h, h⟩⟩
      rw [HE]
      simp only [sum_const, nsmul_eq_mul]
      ring

end NairTenenbaum
