/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.TagPosition

/-! Threshold projections commute with gap sorting and recover tagged positions. -/

@[expose] public noncomputable section
namespace Shellsort

/-- Raising the threshold across one key adds exactly that key's position. -/
theorem thresholdSet_succ_tag {n : ℕ} (p : RankPlacement n) (x : Fin n) :
    thresholdSet p (x.val + 1) = insert (p x) (thresholdSet p x.val) := by
  ext i
  simp only [threshold_mem, Finset.mem_insert]
  constructor
  · intro hi
    by_cases heq : p.symm i = x
    · left
      exact (p.apply_symm_apply i).symm.trans (congrArg p heq)
    · right
      have hne : (p.symm i).val ≠ x.val := by
        intro hv
        exact heq (Fin.ext hv)
      omega
  · rintro (rfl | hi)
    · simp
    · omega

theorem tag_not_in_threshold {n : ℕ} (p : RankPlacement n) (x : Fin n) :
    p x ∉ thresholdSet p x.val := by
  simp [threshold_mem]

/-- The persistent tagged state (lower subset, tagged position) determines
the next tagged position through a singleton threshold difference. -/
theorem lowerStep_tag_difference {n : ℕ} (p : RankPlacement n) (x : Fin n) (k : ℕ) :
    lowerStep (insert (p x) (thresholdSet p x.val)) k \
      lowerStep (thresholdSet p x.val) k = {gapSort p k x} := by
  rw [← thresholdSet_succ_tag, ← gapSort_threshold_commutes,
    ← gapSort_threshold_commutes, thresholdSet_succ_tag]
  simp [tag_not_in_threshold]

/-- Apply the gap passes in order to a rank placement. -/
def sortWord {n : ℕ} (p : RankPlacement n) : List ℕ → RankPlacement n
  | [] => p
  | k :: ks => sortWord (gapSort p k) ks

/-- Apply the sequence of threshold passes to the lower-key slots. -/
def lowerWord {n : ℕ} (B : Finset (Fin n)) : List ℕ → Finset (Fin n)
  | [] => B
  | k :: ks => lowerWord (lowerStep B k) ks

/-- The threshold representation commutes with every fixed finite gap word. -/
theorem sortWord_threshold_commutes {n : ℕ} (p : RankPlacement n)
    (t : ℕ) (ks : List ℕ) :
    thresholdSet (sortWord p ks) t = lowerWord (thresholdSet p t) ks := by
  induction ks generalizing p with
  | nil => rfl
  | cons k ks ih =>
    simp only [sortWord, lowerWord, ih, gapSort_threshold_commutes]

/-- The same two nested thresholds recover the tagged key after any fixed word. -/
theorem lowerWord_tag_difference {n : ℕ} (p : RankPlacement n) (x : Fin n)
    (ks : List ℕ) :
    lowerWord (insert (p x) (thresholdSet p x.val)) ks \
      lowerWord (thresholdSet p x.val) ks = {sortWord p ks x} := by
  rw [← thresholdSet_succ_tag, ← sortWord_threshold_commutes,
    ← sortWord_threshold_commutes, thresholdSet_succ_tag]
  simp [tag_not_in_threshold]

end Shellsort
end
