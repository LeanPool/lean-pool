/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.CompletePrefix

/-!
The unequal-chain boundary in the complete-prefix identity.
The first ell source chains take b+1 positions, the rest take b.
All statements are about actual finite counts, with no probabilistic premise.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators

theorem sum_short_prefix (h ell : ℕ) (hell : ell ≤ h) (f : ℕ → ℕ) :
    (∑ s ∈ Finset.range h, if s < ell then f s else 0) =
      ∑ s ∈ Finset.range ell, f s := by
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range h).filter (fun s => s < ell) = Finset.range ell := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]

theorem sourcePrefixCount_succ (h g j s b : ℕ) :
    sourcePrefixCount h g j s (b + 1) = sourcePrefixCount h g j s b +
      if (s + h * b) % g = j then 1 else 0 := by
  exact Finset.sum_range_succ _ _

theorem mixed_prefix_count (h g j b ell : ℕ) (hell : ell ≤ h) :
    (∑ s ∈ Finset.range h, sourcePrefixCount h g j s
      (if s < ell then b + 1 else b)) =
      residuePrefixCount g j (h * b + ell) := by
  calc
    (∑ s ∈ Finset.range h, sourcePrefixCount h g j s
        (if s < ell then b + 1 else b)) =
        (∑ s ∈ Finset.range h, sourcePrefixCount h g j s b) +
        (∑ s ∈ Finset.range h, if s < ell then
          (if (s + h * b) % g = j then 1 else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s < ell
      · simp only [ite_eq_left hs, sourcePrefixCount_succ]
      · simp only [ite_eq_right hs, add_zero]
    _ = residuePrefixCount g j (h * b) +
        (∑ s ∈ Finset.range ell, if (s + h * b) % g = j then 1 else 0) := by
      rw [complete_prefix_count, sum_short_prefix h ell hell]
    _ = residuePrefixCount g j (h * b + ell) := by
      unfold residuePrefixCount
      rw [Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      simp [Nat.add_comm]

theorem mixed_prefix_lengths (h b ell : ℕ) (hell : ell ≤ h) :
    (∑ s ∈ Finset.range h, if s < ell then b + 1 else b) = h * b + ell := by
  calc
    (∑ s ∈ Finset.range h, if s < ell then b + 1 else b) =
        (∑ _s ∈ Finset.range h, b) +
        (∑ s ∈ Finset.range h, if s < ell then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    _ = h * b + ell := by
      rw [sum_short_prefix h ell hell (fun _ => 1)]
      simp

theorem mixed_prefix_residual (h g j b ell : ℕ)
    (hell : ell ≤ h) (hg : 0 < g) (hj : j < g) :
    (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s
        (if s < ell then b + 1 else b) : ℤ) -
        ((if s < ell then b + 1 else b : ℕ) : ℤ))) =
      phaseResidual g j (h * b + ell) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Nat.cast_sum, mixed_prefix_count h g j b ell hell]
  rw [← Nat.cast_sum, mixed_prefix_lengths h b ell hell]
  exact counted_residual_eq_phase g j (h * b + ell) hg hj

theorem mixed_prefix_balance (h g j b ell : ℕ)
    (hell : ell ≤ h) (hg : 0 < g) (hj : j < g) :
    0 ≤ (j : ℤ) + (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s
        (if s < ell then b + 1 else b) : ℤ) -
        ((if s < ell then b + 1 else b : ℕ) : ℤ))) ∧
    (j : ℤ) + (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s
        (if s < ell then b + 1 else b) : ℤ) -
        ((if s < ell then b + 1 else b : ℕ) : ℤ))) ≤ (g : ℤ) - 1 := by
  rw [mixed_prefix_residual h g j b ell hell hg hj]
  have hbounds := phaseResidual_bounds g j (h * b + ell) hg hj
  omega

end Shellsort
