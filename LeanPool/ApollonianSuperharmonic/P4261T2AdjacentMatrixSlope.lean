/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector

-- [TABLET NODE: P4261T2AdjacentMatrixSlope]

/-!
# P4261T2AdjacentMatrixSlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2AdjacentMatrixSlope
    (C : BandCircle) (T U : ProtoTile) (h k : PartialOdometer)
    (hadj : LeftLatticeAdjacent C T U h k) :
    ∃ p r : Real × Real,
      PartialOdometerSlope h = some p ∧ PartialOdometerSlope k = some r ∧
      r.1 - p.1 = CircleMatrix C 0 0 * ((TileCentroid U).1 - (TileCentroid T).1) +
        CircleMatrix C 0 1 * ((TileCentroid U).2 - (TileCentroid T).2) ∧
      r.2 - p.2 = CircleMatrix C 1 0 * ((TileCentroid U).1 - (TileCentroid T).1) +
        CircleMatrix C 1 1 * ((TileCentroid U).2 - (TileCentroid T).2) := by
-- BODY
  obtain ⟨_, _, p, r, hp, hr, hcase⟩ := hadj
  refine ⟨p, r, hp, hr, ?_⟩
  rcases hcase with ⟨_, o, v, _, hc, hs, ht⟩ | ⟨q, i, e, hq, hC, hc, hs, ht⟩
  · have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    change (TileCentroid U).1 - (TileCentroid T).1 = (v.re : Real) at hc0
    change (TileCentroid U).2 - (TileCentroid T).2 = (v.im : Real) at hc1
    exact ⟨by rw [hc0, hc1]; exact hs, by rw [hc0, hc1]; exact ht⟩
  · have hin := CircleMatrixIncomingVector C q hq.1 hC i
    have hin0 := congrFun hin 0
    have hin1 := congrFun hin 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hin0 hin1
    have hc0 := congrArg Prod.fst hc
    have hc1 := congrArg Prod.snd hc
    change (TileCentroid U).1 - (TileCentroid T).1 =
      (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q i.succ) (q 0)).re : Real) at hc0
    change (TileCentroid U).2 - (TileCentroid T).2 =
      (if e = true then (1 : Real) else -1) *
        ((BandVectors.1 (q i.succ) (q 0)).im : Real) at hc1
    constructor
    · rw [hc0, hc1, hs]
      linear_combination -(if e = true then (1 : Real) else -1) * hin0
    · rw [hc0, hc1, ht]
      linear_combination -(if e = true then (1 : Real) else -1) * hin1

end ApollonianSuperharmonic

end
