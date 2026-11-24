/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.FirstPassMoments
public import LeanPool.ShellsortMean.ChainBitCounts
public import LeanPool.ShellsortMean.OwnerSlice

/-! An upper bound for the uniform mean footrule after the first gap pass. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- First-pass tag displacement determined by the slots holding lower keys. -/
def firstPassSubsetDisplacement {n : ℕ} (h : ℕ) (i : Fin n) (B : Finset (Fin n)) : ℝ :=
  ((i.val % h : ℕ) : ℝ) + (h : ℝ) * chainLowerCount B h (i.val % h) - B.card

theorem actual_onePass_tag_displacement {n : ℕ} (p : RankPlacement n)
    (h : ℕ) (hh : 0 < h) (i : Fin n) :
    ((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ) =
      firstPassSubsetDisplacement h i (tagLowerState p i).val := by
  have hp := gapSort_tag_position p h hh (p.symm i)
  rw [Equiv.apply_symm_apply] at hp
  rw [hp]
  unfold firstPassSubsetDisplacement
  rw [tagLowerState_card]
  push_cast
  rfl

/-- Exact equality of the original-position bit observable and the actual
tagged-subset displacement formula; the unused tag bit contributes zero. -/
theorem fullBits_onePass_displacement {n : ℕ} (h : ℕ) (i : Fin n) (z : Fin n → Bool) :
    firstPassSubsetDisplacement h i (fullBitsSubset i z) =
      firstPassBitDisplacement h i z := by
  have hb : ((fullBitsSubset i z).card : ℝ) =
      ∑ a : Fin n, if a ≠ i ∧ z a = true then (1 : ℝ) else 0 := by
    rw [fullBitsSubset_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rfl
  have hc : (chainLowerCount (fullBitsSubset i z) h (i.val % h) : ℝ) =
      ∑ a : Fin n, if (a ≠ i ∧ z a = true) ∧ a.val % h = i.val % h
        then (1 : ℝ) else 0 := by
    rw [chainLowerCount, fullBitsSubset_filter, Finset.filter_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rfl
  unfold firstPassSubsetDisplacement firstPassBitDisplacement
  rw [hb, hc, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold firstPassCoefficient
  by_cases ha : a = i <;> by_cases hz : z a = true <;>
    by_cases hr : a.val % h = i.val % h <;> simp [ha, hz, hr]

/-- Real uniform-permutation bound for the key initially at position i. -/
theorem uniform_onePass_tag_abs_bound {n : ℕ} (h : ℕ) (hh : 0 < h) (i : Fin n) :
    uniformAverage (fun p : RankPlacement n =>
      |((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) ≤
      (h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2 := by
  simp_rw [actual_onePass_tag_displacement _ h hh i]
  apply uniform_tagged_mean_le_of_full_bernoulli_bound i
    (fun B => |firstPassSubsetDisplacement h i B.val|)
  intro t ht0 ht1
  change mean (bernoulliVectorWeight t n)
    (fun z => |firstPassSubsetDisplacement h i (fullBitsSubset i z)|) ≤ _
  simp_rw [fullBits_onePass_displacement]
  exact firstPassBitDisplacement_absMean_bound h hh i t ⟨ht0, ht1⟩

theorem onePass_footrule_by_original_positions {n : ℕ} (p : RankPlacement n) (h : ℕ) :
    footrule (gapSort p h) =
      ∑ i : Fin n, |((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)| := by
  unfold footrule transport
  simp only [Equiv.refl_apply]
  exact (p.symm.sum_comp (fun x => |((gapSort p h x).val : ℝ) - (x.val : ℝ)|)).symm

theorem uniform_onePass_footrule_by_original_positions (n h : ℕ) :
    uniformAverage (n := n) (fun p => footrule (gapSort p h)) =
      ∑ i : Fin n, uniformAverage (fun p : RankPlacement n =>
        |((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) := by
  simp_rw [onePass_footrule_by_original_positions]
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

/-- End-to-end first-pass footrule bound for actual uniform permutations.
All source-law, mean, variance and finite-boundary estimates are proved. -/
theorem uniform_onePass_footrule_bound (n h : ℕ) (hh : 0 < h) :
    uniformAverage (n := n) (fun p => footrule (gapSort p h)) ≤
      (n : ℝ) * ((h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2) := by
  rw [uniform_onePass_footrule_by_original_positions]
  calc
    _ ≤ ∑ _i : Fin n, ((h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2) :=
      Finset.sum_le_sum (fun i _ => uniform_onePass_tag_abs_bound h hh i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Shellsort
end
