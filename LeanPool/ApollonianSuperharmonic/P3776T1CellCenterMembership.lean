/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: P3776T1CellCenterMembership]

/-!
# P3776T1CellCenterMembership

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3776T1CellCenterMembership (T : ProtoTile) (q : LatticeCell) :
    GaussianRealPoint q + ((1 / 2, 1 / 2) : Real × Real) ∈ TileRealization T ↔
      q ∈ T.cells := by
-- BODY
  constructor
  · intro h
    simp only [TileRealization, Set.mem_iUnion] at h
    obtain ⟨x, hx, hpoint⟩ := h
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      GaussianRealPoint, Prod.fst_add, Prod.snd_add] at hpoint
    have hre : x.re = q.re := by
      have hlow : (x.re : Real) < (q.re : Real) + 1 := by linarith [hpoint.1.1]
      have hhigh : (q.re : Real) < (x.re : Real) + 1 := by linarith [hpoint.2.1]
      have hl : x.re < q.re + 1 := by exact_mod_cast hlow
      have hh : q.re < x.re + 1 := by exact_mod_cast hhigh
      omega
    have him : x.im = q.im := by
      have hlow : (x.im : Real) < (q.im : Real) + 1 := by linarith [hpoint.1.2]
      have hhigh : (q.im : Real) < (x.im : Real) + 1 := by linarith [hpoint.2.2]
      have hl : x.im < q.im + 1 := by exact_mod_cast hlow
      have hh : q.im < x.im + 1 := by exact_mod_cast hhigh
      omega
    have heq : x = q := by ext <;> assumption
    simpa [heq] using hx
  · intro hq
    apply Set.mem_iUnion.mpr
    refine ⟨q, Set.mem_iUnion.mpr ⟨hq, ?_⟩⟩
    norm_num [ClosedSquareRealization, GaussianRealPoint, Set.mem_Icc, Prod.le_def]

end ApollonianSuperharmonic

end
