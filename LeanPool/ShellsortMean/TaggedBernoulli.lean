/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.TaggedLaw
public import LeanPool.ShellsortMean.SubsetBits

/-!
Exact input-law bridge: a uniformly random permutation, tagged at one fixed
original position, is a beta mixture of independent Bernoulli bits at the
other original positions. This is not independence of later sorting states.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators

theorem factorialSubsetWeight_tagged_bits {n : ℕ} (i : Fin n)
    (x : {j : Fin n // j ≠ i} → Bool) :
    factorialSubsetWeight x =
      (((subsetOfBits i x).card.factorial : ℝ) *
        ((n - 1 - (subsetOfBits i x).card).factorial : ℝ) / (n.factorial : ℝ)) := by
  have hc := omittedPosition_card i
  simp only [Fintype.card_fin] at hc
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by omega
  have hn : n - 1 + 1 = n := by omega
  simp only [factorialSubsetWeight, subsetOfBits_card, hcard, hn]

/-- Exact finite expectation after changing from subsets to original-position bits. -/
theorem uniform_tagged_bits_mean {n : ℕ} (i : Fin n) (f : TaggedSubset i → ℝ) :
    uniformAverage (fun p : RankPlacement n => f (tagLowerState p i)) =
      mean factorialSubsetWeight (fun x => f ((omittedBitsSubsetEquiv i) x)) := by
  rw [uniform_tagged_state_mean]
  unfold mean
  calc
    _ = ∑ x : {j : Fin n // j ≠ i} → Bool,
        (((((omittedBitsSubsetEquiv i) x).val.card.factorial : ℝ) *
          ((n - 1 - ((omittedBitsSubsetEquiv i) x).val.card).factorial : ℝ) /
          (n.factorial : ℝ)) * f ((omittedBitsSubsetEquiv i) x)) :=
      ((omittedBitsSubsetEquiv i).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [factorialSubsetWeight_tagged_bits]
      rfl

/-- Uniform permutations and the original-position Bernoulli mixture have exactly
the same expectation for every tagged-state observable, including arbitrary signs. -/
theorem uniform_tagged_bernoulli_mixture {n : ℕ} (i : Fin n) (f : TaggedSubset i → ℝ) :
    uniformAverage (fun p : RankPlacement n => f (tagLowerState p i)) =
      ∫ t : ℝ in 0..1,
        mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
          (fun x => f ((omittedBitsSubsetEquiv i) x)) := by
  rw [uniform_tagged_bits_mean, bernoulli_mixture_mean]

/-- A bound proved uniformly in the Bernoulli parameter is a bound on the actual
uniform-permutation average. The observable is allowed to depend on the full subset. -/
theorem uniform_tagged_mean_le_of_bernoulli_bound {n : ℕ} (i : Fin n)
    (f : TaggedSubset i → ℝ) (K : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
        (fun x => f ((omittedBitsSubsetEquiv i) x)) ≤ K) :
    uniformAverage (fun p : RankPlacement n => f (tagLowerState p i)) ≤ K := by
  rw [uniform_tagged_bits_mean]
  exact bernoulli_mixture_mean_le _ K hbound

end Shellsort
