/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.InversionFootrule
public import LeanPool.ShellsortMean.ChainTransport

/-! A chain insertion cost bound in terms of displacement within the chain. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The actual rank of a key within its original residue chain, indexed by
the original chain ordinal. It is computed from the actual threshold set. -/
def actualChainRank {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k)
    (s : Fin k) (v : Fin (sourceTrialLength (n / k) (n % k) s.val)) : ℕ :=
  chainLowerCount (thresholdSet p (chainKeys p k hk s v).val) k s.val

theorem actualChainRank_sorted_position {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) (s : Fin k)
    (v : Fin (sourceTrialLength (n / k) (n % k) s.val)) :
    (gapSort p k (chainKeys p k hk s v)).val = s.val + k * actualChainRank p k hk s v := by
  have h := gapSort_tag_position p k hk (chainKeys p k hk s v)
  simpa only [actualChainRank, chainKeys, Equiv.apply_symm_apply,
    positionChainEquiv_symm_residue] using h

theorem actualChainRank_lt_iff {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) (s : Fin k)
    (v w : Fin (sourceTrialLength (n / k) (n % k) s.val)) :
    actualChainRank p k hk s v < actualChainRank p k hk s w ↔
      chainKeys p k hk s v < chainKeys p k hk s w := by
  have hs := gapSort_sorted p k (chainKeys p k hk s v) (chainKeys p k hk s w) (by
    simp only [gapSort_preserves_residue, chainKeys, Equiv.apply_symm_apply,
      positionChainEquiv_symm_residue])
  change (gapSort p k (chainKeys p k hk s v)).val <
    (gapSort p k (chainKeys p k hk s w)).val ↔ _ at hs
  simpa only [actualChainRank_sorted_position, Nat.add_lt_add_iff_left,
    Nat.mul_lt_mul_left hk] using hs

theorem chainKeys_injective_for_bound {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) : Function.Injective (chainKeys p k hk s) := by
  intro v w hvw
  have hc := (positionChainEquiv n k hk).symm.injective (p.symm.injective hvw)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hc).2

theorem actualChainRank_injective {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (s : Fin k) : Function.Injective (actualChainRank p k hk s) := by
  intro v w he
  apply chainKeys_injective_for_bound p k hk s
  apply (gapSort p k).injective
  apply Fin.ext
  simp only [actualChainRank_sorted_position, he]

/-- The normalized displacement of each actual chain bounds its independently
executed insertion right-shift counter. -/
theorem chainInsertionCost_le_displacement {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) (s : Fin k) :
    ((insertionExecution (List.ofFn (chainKeys p k hk s))).2 : ℝ) ≤
      ∑ v : Fin (sourceTrialLength (n / k) (n % k) s.val),
        |(actualChainRank p k hk s v : ℝ) - (v.val : ℝ)| := by
  rw [insertionExecution_ofFn_count]
  have hc := coordinate_inversions_le_abs_displacement
    (fun v : Fin (sourceTrialLength (n / k) (n % k) s.val) => v.val)
    (actualChainRank p k hk s) Fin.val_injective (actualChainRank_injective p k hk s)
  simpa only [actualChainRank_lt_iff, Fin.val_fin_lt] using hc

theorem chainFootrule_eq_sum_actualChainRank {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    chainFootrule p k = ∑ s : Fin k,
      ∑ v : Fin (sourceTrialLength (n / k) (n % k) s.val),
        |(actualChainRank p k hk s v : ℝ) - (v.val : ℝ)| := by
  unfold chainFootrule
  rw [sum_positions_by_chains n k hk]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  have hd : ((positionChainEquiv n k hk).symm ⟨s, v⟩).val / k = v.val := by
    rw [positionChainEquiv_symm_val, Nat.add_mul_div_left _ _ hk,
      Nat.div_eq_of_lt s.isLt, Nat.zero_add]
  simp only [positionChainEquiv_symm_residue, hd, actualChainRank, chainKeys]

/-- Actual gap inversion count versus actual chain-normalized footrule. -/
theorem gapInversions_le_chainFootrule {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    (gapInversions p k : ℝ) ≤ chainFootrule p k := by
  rw [← gapInsertionCost_eq_gapInversions p k hk, gapInsertionCost,
    chainFootrule_eq_sum_actualChainRank p k hk, Nat.cast_sum]
  exact Finset.sum_le_sum (fun s _ => chainInsertionCost_le_displacement p k hk s)

/-- The classical global deterministic fee bound now has no external
state-to-cost premise: k is any positive integer, including k ≥ n. -/
theorem gapInversions_le_two_footrule_div {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    (gapInversions p k : ℝ) ≤ 2 * footrule p / (k : ℝ) :=
  (gapInversions_le_chainFootrule p k hk).trans (chainFootrule_le_two_footrule_div p k hk)

/-- The fee is successful right shifts of the specified insertion execution;
it is not a claim about arbitrary comparisons, writes, or transport units. -/
theorem gapInsertionCost_le_two_footrule_div {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    (gapInsertionCost p k hk : ℝ) ≤ 2 * footrule p / (k : ℝ) := by
  rw [gapInsertionCost_eq_gapInversions]
  exact gapInversions_le_two_footrule_div p k hk

end Shellsort
end
