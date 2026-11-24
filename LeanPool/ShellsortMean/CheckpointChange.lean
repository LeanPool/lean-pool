/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.TagPosition

/-!
Exact Hamming counts between physical-array checkpoints. These are state
statistics, not insertion shifts and not a formal operational write-cost model.
-/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The number of ranks whose positions differ between the two placements. -/
def checkpointChange {n : ℕ} (p q : RankPlacement n) : ℕ :=
  (Finset.univ.filter (fun x => p x ≠ q x)).card

/-- The number of slots whose occupants differ between the two placements. -/
def checkpointSlotChange {n : ℕ} (p q : RankPlacement n) : ℕ :=
  (Finset.univ.filter (fun i => p.symm i ≠ q.symm i)).card

/-- A zero-one endpoint reward for the key originally in physical position i. -/
def checkpointTagReward {n : ℕ} (p q : RankPlacement n) (i : Fin n) : ℕ :=
  if q (p.symm i) ≠ i then 1 else 0

theorem checkpointChange_eq_sum_keys {n : ℕ} (p q : RankPlacement n) :
    checkpointChange p q = ∑ x : Fin n, if p x ≠ q x then 1 else 0 := by
  simp only [checkpointChange, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem checkpointChange_eq_sum_tags {n : ℕ} (p q : RankPlacement n) :
    checkpointChange p q = ∑ i : Fin n, checkpointTagReward p q i := by
  rw [checkpointChange_eq_sum_keys]
  rw [← p.symm.sum_comp (fun x => if p x ≠ q x then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.apply_symm_apply, checkpointTagReward, ne_comm]

theorem checkpointTagReward_eq_inverse {n : ℕ} (p q : RankPlacement n) (i : Fin n) :
    checkpointTagReward p q i = if p.symm i ≠ q.symm i then 1 else 0 := by
  have he : q (p.symm i) = i ↔ p.symm i = q.symm i := by
    constructor
    · intro h
      simpa using congrArg q.symm h
    · intro h
      rw [h, Equiv.apply_symm_apply]
  simp only [checkpointTagReward, ne_eq, he]

/-- Changed keys and changed physical slots have exactly the same cardinality. -/
theorem checkpointChange_eq_slots {n : ℕ} (p q : RankPlacement n) :
    checkpointChange p q = checkpointSlotChange p q := by
  rw [checkpointChange_eq_sum_tags]
  simp only [checkpointTagReward_eq_inverse]
  simp only [checkpointSlotChange, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem checkpointChange_le_length {n : ℕ} (p q : RankPlacement n) :
    checkpointChange p q ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)

theorem checkpointChange_triangle {n : ℕ} (p q r : RankPlacement n) :
    checkpointChange p r ≤ checkpointChange p q + checkpointChange q r := by
  simp only [checkpointChange_eq_sum_keys]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hpq : p x = q x <;> by_cases hqr : q x = r x <;>
    by_cases hpr : p x = r x <;> simp_all

/-- The change charged to the tagged key by one gap pass. -/
def gapCheckpointReward {n : ℕ} (p : RankPlacement n) (k : ℕ) (i : Fin n) : ℕ :=
  checkpointTagReward p (gapSort p k) i

/-- Actual gap-sorting endpoint formula converted to a zero-one changed-position reward. -/
theorem gapCheckpointReward_position {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (i : Fin n) :
    gapCheckpointReward p k i =
      if i.val % k + k * chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k)
        ≠ i.val then 1 else 0 := by
  have hp := gapSort_tag_position p k hk (p.symm i)
  rw [Equiv.apply_symm_apply] at hp
  unfold gapCheckpointReward checkpointTagReward
  have he : gapSort p k (p.symm i) = i ↔
      i.val % k + k * chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k)
        = i.val := by
    rw [Fin.ext_iff, hp]
  simp only [ne_eq, he]

/-- A key stays put precisely when its local rank equals its original chain ordinal. -/
theorem gapCheckpointReward_chain_rank {n : ℕ} (p : RankPlacement n) (k : ℕ)
    (hk : 0 < k) (i : Fin n) :
    gapCheckpointReward p k i =
      if chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) ≠ i.val / k
        then 1 else 0 := by
  rw [gapCheckpointReward_position p k hk i]
  have he : i.val % k + k * chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k)
      = i.val ↔ chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) = i.val / k := by
    constructor
    · intro heq
      have hm := Nat.mod_add_div i.val k
      have hmul : k * chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k) =
          k * (i.val / k) := by omega
      exact (Nat.mul_left_cancel_iff hk).mp hmul
    · intro heq
      rw [heq, Nat.mod_add_div]
  simp only [ne_eq, he]

/-- The zero-one tagged rewards sum to the exact checkpoint Hamming count. -/
theorem gapCheckpointReward_sum {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    (∑ i : Fin n, gapCheckpointReward p k i) = checkpointSlotChange p (gapSort p k) := by
  rw [← checkpointChange_eq_slots, checkpointChange_eq_sum_tags]
  rfl

end Shellsort
end
