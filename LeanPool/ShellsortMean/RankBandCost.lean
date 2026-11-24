/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.TagThreshold
public import LeanPool.ShellsortMean.GapInsertionBridge

/-! Disjoint accounting of ordinary insertion shifts by rank intervals. -/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Reversed pairs with both ranks inside the half-open interval [a,b). -/
def rankBandPass {n : ℕ} (p : RankPlacement n) (k a b : ℕ) : ℕ :=
  ∑ ij ∈ gapPositionPairs n k,
    if a ≤ (p.symm ij.2).val ∧ p.symm ij.2 < p.symm ij.1 ∧ (p.symm ij.1).val < b
    then 1 else 0

/-- Count a pair from the upper and lower children of one rank interval using
only the position sets of three thresholds. -/
def thresholdSplitPass {n : ℕ} (L T U : Finset (Fin n)) (k : ℕ) : ℕ :=
  ∑ ij ∈ gapPositionPairs n k,
    if ij.1 ∈ U ∧ ij.1 ∉ T ∧ ij.2 ∈ T ∧ ij.2 ∉ L then 1 else 0

theorem rankBandPass_split {n : ℕ} (p : RankPlacement n) (k a m b : ℕ)
    (ham : a ≤ m) (hmb : m ≤ b) :
    rankBandPass p k a b =
      rankBandPass p k a m + thresholdSplitPass (thresholdSet p a)
        (thresholdSet p m) (thresholdSet p b) k + rankBandPass p k m b := by
  unfold rankBandPass thresholdSplitPass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [threshold_mem, Fin.lt_def]
  split_ifs <;> omega

theorem rankBandPass_full {n : ℕ} (p : RankPlacement n) (k : ℕ) :
    rankBandPass p k 0 n = gapInversions p k := by
  unfold rankBandPass gapInversions
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ij _
  simp [(p.symm ij.1).isLt]

/-- Covers words with any number of positive gaps. An optional terminal gap
one or an ordering of gaps is not required for these identities. -/
def rankBandWord {n : ℕ} (p : RankPlacement n) (a b : ℕ) :
    List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => rankBandPass p k.val a b + rankBandWord (gapSort p k.val) a b ks

/-- A cross-child count evaluated from the three binary states alone. -/
def thresholdSplitWord {n : ℕ} (L T U : Finset (Fin n)) :
    List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => thresholdSplitPass L T U k.val +
      thresholdSplitWord (lowerStep L k.val) (lowerStep T k.val) (lowerStep U k.val) ks

/-- The shift counter of executed insertion passes at the true checkpoints. -/
def ordinaryWordShifts {n : ℕ} (p : RankPlacement n) :
    List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => gapInsertionCost p k.val k.property + ordinaryWordShifts (gapSort p k.val) ks

theorem rankBandWord_full {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    rankBandWord p 0 n ks = ordinaryWordShifts p ks := by
  induction ks generalizing p with
  | nil => rfl
  | cons k ks ih =>
    simp only [rankBandWord, ordinaryWordShifts, rankBandPass_full, ih,
      gapInsertionCost_eq_gapInversions]

/-- Every paid pair in the parent lies in exactly one of three classes.
Iterating this equality over nested rank splits never counts a shift twice. -/
theorem rankBandWord_split {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k})
    (a m b : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    rankBandWord p a b ks =
      rankBandWord p a m ks +
        thresholdSplitWord (thresholdSet p a) (thresholdSet p m) (thresholdSet p b) ks +
        rankBandWord p m b ks := by
  induction ks generalizing p with
  | nil => rfl
  | cons k ks ih =>
    simp only [rankBandWord, thresholdSplitWord]
    rw [rankBandPass_split p k.val a m b ham hmb, ih (gapSort p k.val)]
    simp only [gapSort_threshold_commutes]
    omega

theorem ordinaryWordShifts_split {n : ℕ} (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) (m : ℕ) (hm : m ≤ n) :
    ordinaryWordShifts p ks = rankBandWord p 0 m ks +
      thresholdSplitWord (thresholdSet p 0) (thresholdSet p m) (thresholdSet p n) ks +
      rankBandWord p m n ks := by
  rw [← rankBandWord_full]
  exact rankBandWord_split p ks 0 m n (Nat.zero_le _) hm

/-- An ordered binary subdivision. The bounds in the type enforce that the
children partition the parent rank interval even with uneven block sizes. -/
inductive RankCutTree : ℕ → ℕ → Type
  | leaf (a b : ℕ) : RankCutTree a b
  | split {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b)
      (left : RankCutTree a m) (right : RankCutTree m b) : RankCutTree a b

namespace RankCutTree

/-- Sum only the cross-child rewards of retained splits. -/
def visible {n a b : ℕ} (tree : RankCutTree a b) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) : ℕ :=
  match tree with
  | .leaf _ _ => 0
  | @RankCutTree.split lo m hi _ _ left right =>
      thresholdSplitWord (thresholdSet p lo) (thresholdSet p m) (thresholdSet p hi) ks +
        left.visible p ks + right.visible p ks

/-- The cost hidden within the terminal rank blocks. -/
def hidden {n a b : ℕ} (tree : RankCutTree a b) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) : ℕ :=
  match tree with
  | .leaf lo hi => rankBandWord p lo hi ks
  | .split _ _ left right => left.hidden p ks + right.hidden p ks

theorem account {n a b : ℕ} (tree : RankCutTree a b) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    tree.visible p ks + tree.hidden p ks = rankBandWord p a b ks := by
  induction tree with
  | leaf lo hi => simp [visible, hidden]
  | @split lo m hi ham hmb left right ih₁ ih₂ =>
    rw [rankBandWord_split p ks lo m hi ham hmb]
    simp only [visible, hidden]
    omega

/-- An exact lower certificate for any choice of retained rank cuts. -/
theorem visible_le_ordinaryWordShifts {n : ℕ} (tree : RankCutTree 0 n)
    (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    tree.visible p ks ≤ ordinaryWordShifts p ks := by
  rw [← rankBandWord_full, ← tree.account]
  exact Nat.le_add_right _ _

/-- A subtree with only empty or one-rank leaves resolves every eligible shift. -/
def resolved {a b : ℕ} (tree : RankCutTree a b) : Prop :=
  match tree with
  | .leaf lo hi => hi ≤ lo + 1
  | .split _ _ left right => left.resolved ∧ right.resolved

theorem hidden_eq_zero_of_resolved {n a b : ℕ} (tree : RankCutTree a b)
    (h : tree.resolved) (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    tree.hidden p ks = 0 := by
  induction tree with
  | leaf lo hi =>
    change hi ≤ lo + 1 at h
    change rankBandWord p lo hi ks = 0
    induction ks generalizing p with
    | nil => rfl
    | cons k ks ih =>
      rw [rankBandWord, ih (gapSort p k.val), Nat.add_zero]
      apply Finset.sum_eq_zero
      intro ij _
      simp only [Fin.lt_def]
      split_ifs <;> omega
  | split ham hmb left right ih₁ ih₂ =>
    exact Nat.add_eq_zero_iff.mpr ⟨ih₁ h.1, ih₂ h.2⟩

theorem visible_eq_ordinaryWordShifts_of_resolved {n : ℕ} (tree : RankCutTree 0 n)
    (h : tree.resolved) (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    tree.visible p ks = ordinaryWordShifts p ks := by
  rw [← rankBandWord_full, ← tree.account, tree.hidden_eq_zero_of_resolved h, Nat.add_zero]

end RankCutTree

/-- All on-chain position pairs restricted to the same rank band, irrespective
of their internal order. The endpoints of the band are the only data needed. -/
def thresholdBandRoomPass {n : ℕ} (L U : Finset (Fin n)) (k : ℕ) : ℕ :=
  ∑ ij ∈ gapPositionPairs n k,
    if ij.1 ∈ U ∧ ij.1 ∉ L ∧ ij.2 ∈ U ∧ ij.2 ∉ L then 1 else 0

theorem rankBandPass_le_room {n : ℕ} (p : RankPlacement n) (k a b : ℕ) :
    rankBandPass p k a b ≤ thresholdBandRoomPass (thresholdSet p a) (thresholdSet p b) k := by
  unfold rankBandPass thresholdBandRoomPass
  apply Finset.sum_le_sum
  intro ij _
  simp only [threshold_mem, Fin.lt_def]
  split_ifs <;> omega

/-- The total band-crossing budget along the successive threshold states of a gap word. -/
def thresholdBandRoomWord {n : ℕ} (L U : Finset (Fin n)) :
    List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => thresholdBandRoomPass L U k.val +
      thresholdBandRoomWord (lowerStep L k.val) (lowerStep U k.val) ks

theorem rankBandWord_le_room {n : ℕ} (p : RankPlacement n)
    (a b : ℕ) (ks : List {k : ℕ // 0 < k}) :
    rankBandWord p a b ks ≤ thresholdBandRoomWord (thresholdSet p a) (thresholdSet p b) ks := by
  induction ks generalizing p with
  | nil => exact le_rfl
  | cons k ks ih =>
    apply Nat.add_le_add (rankBandPass_le_room p k.val a b)
    simpa only [gapSort_threshold_commutes] using ih (gapSort p k.val)

namespace RankCutTree

/-- Unresolved same-band pairs along the schedule, evaluated from the
endpoint thresholds for each leaf. -/
def room {n a b : ℕ} (tree : RankCutTree a b) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) : ℕ :=
  match tree with
  | .leaf lo hi => thresholdBandRoomWord (thresholdSet p lo) (thresholdSet p hi) ks
  | .split _ _ left right => left.room p ks + right.room p ks

theorem hidden_le_room {n a b : ℕ} (tree : RankCutTree a b) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) : tree.hidden p ks ≤ tree.room p ks := by
  induction tree with
  | leaf lo hi => exact rankBandWord_le_room p lo hi ks
  | split ham hmb left right ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂

/-- Inputwise two-sided certificate computed solely from nested coarse
thresholds and the stipulated gap schedule. -/
theorem ordinaryWordShifts_sandwich {n : ℕ} (tree : RankCutTree 0 n)
    (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    tree.visible p ks ≤ ordinaryWordShifts p ks ∧
      ordinaryWordShifts p ks ≤ tree.visible p ks + tree.room p ks := by
  refine ⟨tree.visible_le_ordinaryWordShifts p ks, ?_⟩
  rw [← rankBandWord_full, ← tree.account]
  exact Nat.add_le_add_left (tree.hidden_le_room p ks) _

end RankCutTree

end Shellsort
end
