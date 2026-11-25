/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import LeanPool.ShellsortMean.ResidueCount
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Counts and residuals over complete blocks of a source prefix. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

theorem sum_prefix_blocks (h b : ℕ) (f : ℕ → ℕ) :
    (∑ s ∈ Finset.range h, ∑ v ∈ Finset.range b, f (s + h * v)) =
      ∑ i ∈ Finset.range (h * b), f i := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    omega

/-- Count how many of the first b positions of source chain s hit target j. -/
def sourcePrefixCount (h g j s b : ℕ) : ℕ :=
  ∑ v ∈ Finset.range b, if (s + h * v) % g = j then 1 else 0

/-- Complete source prefixes exactly partition one physical prefix. -/
theorem complete_prefix_count (h g j b : ℕ) :
    (∑ s ∈ Finset.range h, sourcePrefixCount h g j s b) =
      residuePrefixCount g j (h * b) := by
  exact sum_prefix_blocks h b (fun i => if i % g = j then 1 else 0)

/-- The deterministic cancellation underlying the reference-mean argument. -/
theorem complete_prefix_residual (h g j b : ℕ) (hg : 0 < g) (hj : j < g) :
    (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s b : ℤ) - (b : ℤ))) =
      phaseResidual g j (h * b) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Nat.cast_sum, complete_prefix_count]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  convert counted_residual_eq_phase g j (h * b) hg hj using 1; push_cast; ring

theorem complete_prefix_balance (h g j b : ℕ) (hg : 0 < g) (hj : j < g) :
    0 ≤ (j : ℤ) + (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s b : ℤ) - (b : ℤ))) ∧
    (j : ℤ) + (∑ s ∈ Finset.range h,
      ((g : ℤ) * (sourcePrefixCount h g j s b : ℤ) - (b : ℤ))) ≤ (g : ℤ) - 1 := by
  rw [complete_prefix_residual h g j b hg hj]
  have hbounds := phaseResidual_bounds g j (h * b) hg hj
  omega

end Shellsort
