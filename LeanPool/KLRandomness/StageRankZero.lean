/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRank

/-!
# A finite zero-rank test for concrete sparse blocks

Partial unread rank can be recognized without computing its numerical value:
the remaining matrix is nonzero, but it is not surjective. Together with the
full-rank bridge, this exact zero test supplies finite predicates for the
stage construction's partial-rank probabilities.
-/

@[expose] public section

noncomputable section

namespace Klr.StageRank

open SparseListSearch SparseListWeights SparseSearch SparseListCode StageCandidate
open AffineCode AffineObservation RandomMatrix
open scoped BigOperators

variable {M m r : ℕ}

theorem remainingRank_eq_zero_iff_unreadMap_eq_zero (B : AffineBlock)
    (π : ScanRule) (v : List Bool) :
    B.remainingRank π v = 0 ↔ unreadMap B.matrix (B.observed π v) = 0 := by
  rw [AffineBlock.remainingRank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]

/-- Rank zero means that every unqueried pool column is zero. -/
theorem remainingRank_eq_zero_iff_columns
    (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (π : ScanRule) (v : List Bool) :
    (block e he a ha y).remainingRank π v = 0 ↔
      ∀ j : Fin M, j ∈ unreadPool e π v → columns a M r j = 0 := by
  classical
  rw [remainingRank_eq_zero_iff_unreadMap_eq_zero]
  constructor
  · intro hzero j hj
    by_cases hs : j ∈ support M a
    · let p : (block e he a ha y).support := positionEquiv e he a ⟨j, hs⟩
      have hp : p ∉ (block e he a ha y).observed π v :=
        (mem_unreadPool e π v j).mp hj
      have h := (unreadMap_single (block e he a ha y).matrix
        ((block e he a ha y).observed π v) p hp).trans
          (block_matrix_single e he a ha y ⟨j, hs⟩)
      rw [hzero, LinearMap.zero_apply] at h
      exact h.symm
    · exact columns_zero_off_support ha hs
  · intro hcols
    apply LinearMap.ext
    intro x
    change (∑ j : support M a,
      (extendUnread ((block e he a ha y).observed π v) x)
        (positionEquiv e he a j) • columns a M r j.val) = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : e j.val ∈ π.queriedPositions v
    · have ho : positionEquiv e he a j ∈ (block e he a ha y).observed π v := hj
      rw [extendUnread_apply_of_mem _ x _ ho, zero_smul]
    · rw [hcols j.val ((mem_unreadPool e π v j.val).mpr hj), smul_zero]

/-- The actual Boolean masked matrix is zero exactly when all selected
columns vanish; dimensions are supplied by the successful entry verifier. -/
theorem masked_matrix_eq_zero_iff_columns {a : Entry} (ha : GoodEntry M m r a)
    (d : List Bool) :
    matrix (maskCode a.2 d) = 0 ↔
      ∀ j : Fin M, j ∈ maskSet M d → columns a M r j = 0 := by
  have hw := ha.2.2.1
  have hr := ha.2.2.2.1
  cases hw
  cases hr
  rw [matrix_maskCode]
  constructor
  · intro h j hj
    have hd := (mem_maskSet (width a.2) d j).mp hj
    funext i
    change matrix a.2 i j = (0 : ZMod 2)
    have hi := congrFun (congrFun h i) j
    change (if d.getD j.val false then matrix a.2 i j else 0) = (0 : ZMod 2) at hi
    simpa only [hd, Bool.true_eq, ↓reduceIte] using hi
  · intro h
    funext i j
    change (if d.getD j.val false then matrix a.2 i j else 0) = (0 : ZMod 2)
    cases hd : d.getD j.val false with
    | false => rfl
    | true =>
      have hz := congrFun (h j ((mem_maskSet _ _ _).mpr hd)) i
      change matrix a.2 i j = (0 : ZMod 2) at hz
      simpa only [Bool.true_eq, ↓reduceIte] using hz

/-- Exact finite zero-rank test for the affine block embedded on a concrete pool. -/
theorem remainingRank_eq_zero_iff_masked_matrix_eq_zero
    (e : Fin M → ℕ) (he : Function.Injective e) (a : Entry)
    (ha : GoodEntry M m r a) (y : Fin r → ZMod 2)
    (π : ScanRule) (v : List Bool) :
    (block e he a ha y).remainingRank π v = 0 ↔
      matrix (maskCode a.2 (mask (unreadPool e π v))) = 0 := by
  rw [remainingRank_eq_zero_iff_columns e he a ha y π v,
    masked_matrix_eq_zero_iff_columns ha, maskSet_mask]

end Klr.StageRank
