/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapMonotone
public import LeanPool.ShellsortMean.CheckpointChange

/-! Transport distances for chain sorting and their comparison with global footrule. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Chain-normalized footrule: actual local key rank versus the original ordinal
inside its residue chain. This statistic is not an insertion-shift counter. -/
def chainFootrule {n : ℕ} (p : RankPlacement n) (k : ℕ) : ℝ :=
  ∑ i : Fin n,
    |(chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) : ℝ) -
      ((i.val / k : ℕ) : ℝ)|

theorem transport_by_original_positions {n : ℕ} (p q : RankPlacement n) :
    transport p q = ∑ i : Fin n, |(i.val : ℝ) - ((q (p.symm i)).val : ℝ)| := by
  unfold transport
  have hs := p.symm.sum_comp (fun x => |((p x).val : ℝ) - ((q x).val : ℝ)|)
  simpa only [Equiv.apply_symm_apply] using hs.symm

/-- An actual chain displacement is precisely k times the normalized local displacement. -/
theorem gapSort_tag_transport_eq {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (i : Fin n) :
    |(i.val : ℝ) - ((gapSort p k (p.symm i)).val : ℝ)| =
      (k : ℝ) *
      |(chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) : ℝ) -
        ((i.val / k : ℕ) : ℝ)| := by
  have hp := congrArg (fun z : ℕ => (z : ℝ)) (gapSort_tag_position p k hk (p.symm i))
  simp only [Equiv.apply_symm_apply] at hp
  push_cast at hp
  have hi := congrArg (fun z : ℕ => (z : ℝ)) (Nat.mod_add_div i.val k)
  push_cast at hi
  have hd : ((gapSort p k (p.symm i)).val : ℝ) - (i.val : ℝ) =
      (k : ℝ) * ((chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) : ℝ) -
        ((i.val / k : ℕ) : ℝ)) := by nlinarith [hp, hi]
  rw [abs_sub_comm, hd, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]

/-- Exact state-to-transport bridge, derived from the actual sorting operator. -/
theorem gapSort_transport_eq_mul_chainFootrule {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) :
    transport p (gapSort p k) = (k : ℝ) * chainFootrule p k := by
  rw [transport_by_original_positions]
  simp_rw [gapSort_tag_transport_eq p k hk]
  exact (Finset.mul_sum _ _ _).symm

theorem chainFootrule_nonneg {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    0 ≤ chainFootrule p k :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Global and local footrule retain the true residual state after this pass. -/
theorem global_chainFootrule_triangle {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) :
    |footrule p - (k : ℝ) * chainFootrule p k| ≤ footrule (gapSort p k) := by
  rw [← gapSort_transport_eq_mul_chainFootrule p k hk, abs_le]
  have h1 := footrule_triangle p (gapSort p k)
  have h2 := transport_le_footrules p (gapSort p k)
  constructor <;> linarith

theorem chainFootrule_le_two_footrule_div {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) :
    chainFootrule p k ≤ 2 * footrule p / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (le_div_iff₀ hkR).mpr
  rw [mul_comm, ← gapSort_transport_eq_mul_chainFootrule p k hk]
  exact gapSort_transport_le_two_footrule p k

theorem indicator_ne_le_abs_nat_sub (a b : ℕ) :
    (if a ≠ b then (1 : ℝ) else 0) ≤ |(a : ℝ) - (b : ℝ)| := by
  by_cases hab : a = b
  · simp only [hab, ne_eq, not_true_eq_false, ite_false, sub_self, abs_zero, le_refl]
  · simp only [hab, ne_eq, not_false_eq_true, ite_true]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hR : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- Each changed physical slot needs at least one unit of normalized chain
transport. The cost here is endpoint Hamming change, not insertion movement. -/
theorem gapCheckpointChange_le_chainFootrule {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) :
    (checkpointSlotChange p (gapSort p k) : ℝ) ≤ chainFootrule p k := by
  rw [← gapCheckpointReward_sum]
  push_cast
  unfold chainFootrule
  apply Finset.sum_le_sum
  intro i _
  rw [gapCheckpointReward_chain_rank p k hk i]
  push_cast
  exact indicator_ne_le_abs_nat_sub _ _

end Shellsort
end
