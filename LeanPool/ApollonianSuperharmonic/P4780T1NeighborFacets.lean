/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4780T1ActiveFacets

-- [TABLET NODE: P4780T1NeighborFacets]

/-!
# P4780T1NeighborFacets

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1NeighborFacets (j : Fin 6) :
    let d : Int × Int := ![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j
    P4715T1Hexagon ∩
      ((fun p : Real × Real => p + ((d.1 : Real), (d.2 : Real))) ''
        P4715T1Hexagon) =
    P4715T1Arc (P4715T1BoundaryCycle j)
      (P4715T1BoundaryCycle (j + 1)) := by
-- BODY
  have ht (c : Real × Real) :
      (fun x : Real × Real => x + c) '' P4715T1Hexagon =
        {p | p-c ∈ P4715T1Hexagon} := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨p-c, hp, sub_add_cancel p c⟩
  dsimp only
  rw [P4780T1ActiveFacets]
  ext p
  fin_cases j
  all_goals
    simp only [P4780T1HullHalfspaces, neg_le_sub_iff_le_add, tsub_le_iff_right, zero_add,
        Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_zero, Int.cast_neg, Int.cast_one,
        ht, Set.mem_ofPred_eq, Prod.snd_sub, sub_neg_eq_add, Prod.fst_sub, sub_zero,
        Set.mem_inter_iff, and_congr_right_iff, and_imp, Fin.reduceFinMk, Matrix.cons_val,
        sub_add_cancel, Fin.zero_eta]
    intro ha1 ha2 ha3 ha4 ha5 ha6
    constructor
    · rintro ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩
      linarith
    · intro he
      exact ⟨by linarith, by linarith, by linarith,
        by linarith, by linarith, by linarith⟩

end ApollonianSuperharmonic

end
