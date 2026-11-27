/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageStep
public import LeanPool.KLRandomness.HorizonAvoidance

/-!
# Finite construction histories and their avoidance cutoffs

A finite history is represented by natural-number indexed blocks and
horizons, with explicit empty padding beyond its length. Its cutoff covers
every old support and every query on every branch through each old protected
horizon. Adding a support above that cutoff preserves disjointness and all
the required future horizon avoidance.
-/

@[expose] public section

noncomputable section

namespace Klr.StageRecursion

open scoped BigOperators

/-- Empty padding imposes no equation and uses no coordinates. -/
def emptyBlock : AffineBlock where
  support := ∅
  rank := 0
  matrix := 0
  fullRank := fun y => ⟨0, Subsingleton.elim _ y⟩
  syndrome := 0

@[simp] theorem emptyBlock_support : emptyBlock.support = ∅ := rfl

/-- Finite history with explicit harmless padding after its last stage. -/
structure History (n : ℕ) where
  /-- The affine blocks selected so far, extended by empty blocks. -/
  blocks : ℕ → AffineBlock
  /-- Finite query horizons recorded by earlier stages. -/
  horizon : ℕ → ℕ
  disjoint : Pairwise (fun i j => Disjoint (blocks i).support (blocks j).support)
  blocks_tail : ∀ k, n ≤ k → blocks k = emptyBlock
  horizon_tail : ∀ k, n ≤ k → horizon k = 0

namespace History

/-- The initial history has no blocks or protected horizons. -/
def empty : History 0 where
  blocks := fun _ => emptyBlock
  horizon := fun _ => 0
  disjoint := by intro i j hij; simp
  blocks_tail := fun _ _ => rfl
  horizon_tail := fun _ _ => rfl

variable {n : ℕ}

/-- One finite contribution to the avoidance cutoff. At stage `j`, strategies
`0, ..., j` must be protected through that stage's common horizon. -/
def boundTerm (s : ℕ → BettingStrategy) (h : History n) (j : Fin n) : ℕ :=
  (h.blocks j.val).support.sup id +
    ∑ i : Fin (j.val + 1), HorizonAvoidance.queryBound (s i.val).normalize.scan
      (h.horizon j.val)

/-- A strict bound for all old support coordinates, and an upper bound for
all earlier protected all-branch query bounds. -/
def cutoff (s : ℕ → BettingStrategy) (h : History n) : ℕ :=
  (∑ j : Fin n, boundTerm s h j) + 1

theorem support_lt_cutoff (s : ℕ → BettingStrategy) (h : History n)
    (j : Fin n) {q : ℕ} (hq : q ∈ (h.blocks j.val).support) : q < cutoff s h := by
  have hs := Finset.le_sup (f := id) hq
  change q ≤ (h.blocks j.val).support.sup id at hs
  have ht : boundTerm s h j ≤ ∑ k : Fin n, boundTerm s h k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold cutoff boundTerm at *
  omega

theorem queryBound_le_cutoff (s : ℕ → BettingStrategy) (h : History n)
    (j : Fin n) (i : ℕ) (hi : i ≤ j.val) :
    HorizonAvoidance.queryBound (s i).normalize.scan (h.horizon j.val) ≤ cutoff s h := by
  let f : Fin (j.val + 1) → ℕ := fun k =>
    HorizonAvoidance.queryBound (s k.val).normalize.scan (h.horizon j.val)
  let ii : Fin (j.val + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  have hs : f ii ≤ ∑ k : Fin (j.val + 1), f k :=
    Finset.single_le_sum (f := f) (s := Finset.univ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ii)
  change HorizonAvoidance.queryBound (s i).normalize.scan (h.horizon j.val) ≤
    ∑ k : Fin (j.val + 1), HorizonAvoidance.queryBound (s k.val).normalize.scan
      (h.horizon j.val) at hs
  have ht : boundTerm s h j ≤ ∑ k : Fin n, boundTerm s h k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold cutoff boundTerm at *
  omega

/-- A support above the cutoff is disjoint from every old block, including
the empty padding. -/
theorem disjoint_of_above (s : ℕ → BettingStrategy) (h : History n)
    (C : AffineBlock) (hC : ∀ q ∈ C.support, cutoff s h ≤ q) (j : ℕ) :
    Disjoint (h.blocks j).support C.support := by
  by_cases hj : j < n
  · apply Finset.disjoint_left.mpr
    intro q hq hqC
    exact (not_lt_of_ge (hC q hqC)) (support_lt_cutoff s h ⟨j, hj⟩ hq)
  · rw [h.blocks_tail j (Nat.le_of_not_gt hj)]
    simp

/-- Extend a finite history by its next block and common horizon. -/
def extend (s : ℕ → BettingStrategy) (h : History n) (C : AffineBlock) (V : ℕ)
    (hC : ∀ q ∈ C.support, cutoff s h ≤ q) : History (n + 1) where
  blocks := Function.update h.blocks n C
  horizon := Function.update h.horizon n V
  disjoint := by
    intro i j hij
    by_cases hi : i = n
    · subst i
      have hj : j ≠ n := Ne.symm hij
      simpa only [Function.update_self, Function.update_of_ne hj] using
        (disjoint_of_above s h C hC j).symm
    · by_cases hj : j = n
      · subst j
        simpa only [Function.update_self, Function.update_of_ne hi] using
          disjoint_of_above s h C hC i
      · simpa only [Function.update_of_ne hi, Function.update_of_ne hj] using h.disjoint hij
  blocks_tail := by
    intro k hk
    rw [Function.update_of_ne (by omega : k ≠ n)]
    exact h.blocks_tail k (by omega)
  horizon_tail := by
    intro k hk
    rw [Function.update_of_ne (by omega : k ≠ n)]
    exact h.horizon_tail k (by omega)

@[simp] theorem extend_blocks_self (s : ℕ → BettingStrategy) (h : History n)
    (C : AffineBlock) (V : ℕ) (hC : ∀ q ∈ C.support, cutoff s h ≤ q) :
    (extend s h C V hC).blocks n = C := Function.update_self _ _ _

@[simp] theorem extend_horizon_self (s : ℕ → BettingStrategy) (h : History n)
    (C : AffineBlock) (V : ℕ) (hC : ∀ q ∈ C.support, cutoff s h ≤ q) :
    (extend s h C V hC).horizon n = V := Function.update_self _ _ _

theorem extend_blocks_of_lt (s : ℕ → BettingStrategy) (h : History n)
    (C : AffineBlock) (V : ℕ) (hC : ∀ q ∈ C.support, cutoff s h ≤ q)
    {j : ℕ} (hj : j < n) : (extend s h C V hC).blocks j = h.blocks j :=
  Function.update_of_ne (Nat.ne_of_lt hj) _ _

theorem extend_horizon_of_lt (s : ℕ → BettingStrategy) (h : History n)
    (C : AffineBlock) (V : ℕ) (hC : ∀ q ∈ C.support, cutoff s h ≤ q)
    {j : ℕ} (hj : j < n) : (extend s h C V hC).horizon j = h.horizon j :=
  Function.update_of_ne (Nat.ne_of_lt hj) _ _

end History

end Klr.StageRecursion
