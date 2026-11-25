/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ConditionalSource
public import LeanPool.ShellsortMean.ProductTransport
public import LeanPool.ShellsortMean.TaggedBernoulli

/-! Removing the owner bit when estimating conditional tagged displacement. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- For a fixed owner count, the dummy owner input does not affect displacement. -/
theorem conditionalSourceDisplacement_ignore_owner (h g m ell : ℕ)
    (owner : Fin h) (y : ℕ)
    (x z : ∀ s : Fin h, Fin (sourceTrialLength m ell s.val) → Bool)
    (hrest : ∀ s, s ≠ owner → x s = z s) :
    conditionalSourceDisplacement h g m ell owner y x =
      conditionalSourceDisplacement h g m ell owner y z := by
  unfold conditionalSourceDisplacement
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  unfold conditionalSourceResidual
  by_cases hs : s = owner
  · simp only [hs, ite_true]
  · simp only [hs, ite_false, hrest s hs]

/-- The owner count may be any function of its complete original chain bits.
Slicing the actual product law and averaging the proved fixed-count bounds
preserves the same uniform L1 estimate. -/
theorem owner_selected_source_absMean_bound (h g m ell : ℕ) (t : ℝ)
    (owner : Fin h)
    (ownerCount : (Fin (sourceTrialLength m ell owner.val) → Bool) → ℕ)
    (ht : 0 ≤ t ∧ t ≤ 1) (hell : ell ≤ h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    mean (conditionalSourceWeight h m ell t)
      (fun x => |conditionalSourceDisplacement h g m ell owner (ownerCount (x owner)) x|) ≤
      ((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2 := by
  have he := productWeight_owner_diagonal (sourceCoordinateWeight h m ell t) owner
    (sourceCoordinateWeight_sum h m ell t owner)
    (fun a x => |conditionalSourceDisplacement h g m ell owner (ownerCount a) x|)
    (fun a x z hxz => congrArg abs
      (conditionalSourceDisplacement_ignore_owner h g m ell owner (ownerCount a) x z hxz))
  change mean (productWeight (sourceCoordinateWeight h m ell t)) _ ≤ _
  rw [he]
  unfold mean
  calc
    _ ≤ ∑ a, sourceCoordinateWeight h m ell t owner a *
        (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (conditionalSourceDisplacement_absMean_bound h g m ell t owner (ownerCount a)
          ht hell hg hc) (sourceCoordinateWeight_nonneg h m ell t ht owner a)
    _ = _ := by
      rw [← Finset.sum_mul, sourceCoordinateWeight_sum, one_mul]

/-- Adding an unused bit at the original tagged position preserves the mean. -/
theorem bernoulli_mean_add_dummy {α : Type*} [Fintype α] [DecidableEq α]
    (i : α) (t : ℝ) (F : ({j : α // j ≠ i} → Bool) → ℝ) :
    mean (productWeight (fun _j : α => bernoulliWeight t))
      (fun x => F (fun j => x j.val)) =
      mean (productWeight (fun _j : {j : α // j ≠ i} => bernoulliWeight t)) F := by
  exact productWeight_mean_ignore_coordinate (β := fun _ : α => Bool)
    (fun _ : α => bernoulliWeight t) i (bernoulliWeight_sum t) F

/-- Actual uniform permutation expectation can be bounded with full original-position
bits, provided the tagged-position bit is ignored by the subset observable. -/
theorem uniform_tagged_mean_le_of_full_bernoulli_bound {n : ℕ} (i : Fin n)
    (f : TaggedSubset i → ℝ) (K : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      mean (productWeight (fun _j : Fin n => bernoulliWeight t))
        (fun x => f ((omittedBitsSubsetEquiv i) (fun j => x j.val))) ≤ K) :
    uniformAverage (fun p : RankPlacement n => f (tagLowerState p i)) ≤ K := by
  apply uniform_tagged_mean_le_of_bernoulli_bound i f K
  intro t ht0 ht1
  rw [← bernoulli_mean_add_dummy i t (fun x => f ((omittedBitsSubsetEquiv i) x))]
  exact hbound t ht0 ht1

end Shellsort
