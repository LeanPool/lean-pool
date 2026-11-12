/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4397T1UnitEdgeCells
public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership
public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P4397T1ReflectedEdgeNotBoundary]

/-!
# P4397T1ReflectedEdgeNotBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4397T1ReflectedEdgeNotBoundary (O : ProtoTile)
    (c : Real × Real) (hsym : CentrallyReflectedAt c O O)
    (a b : GaussianInt) (hadj : FourNeighborAdjacent a b)
    (hreflect : GaussianRealPoint b =
      (2 * c.1 - (GaussianRealPoint a).1,
        2 * c.2 - (GaussianRealPoint a).2)) :
    ({a, b} : Finset GaussianInt) ∉ BoundaryFootprintEdges O := by
-- BODY
  obtain ⟨z, w, hshape⟩ := P4397T1UnitEdgeCells.1 a b hadj
  have hgeom := P4397T1UnitEdgeCells.2 a b z w hshape
  have hre : (a.re : Real) + (b.re : Real) = 2 * c.1 := by
    have h := congrArg Prod.fst hreflect
    dsimp [GaussianRealPoint] at h
    linarith
  have him : (a.im : Real) + (b.im : Real) = 2 * c.2 := by
    have h := congrArg Prod.snd hreflect
    dsimp [GaussianRealPoint] at h
    linarith
  have hsum : (z.re : Real) + (w.re : Real) + 1 = 2 * c.1 ∧
      (z.im : Real) + (w.im : Real) + 1 = 2 * c.2 := by
    rcases hshape with ⟨(⟨ha, hb⟩ | ⟨hb, ha⟩), hw⟩ |
      ⟨(⟨ha, hb⟩ | ⟨hb, ha⟩), hw⟩
    all_goals
      subst a
      subst b
      subst w
      norm_num at hre him ⊢
      constructor <;> linarith
  have image_center (r s : GaussianInt)
      (hr : r ∈ O.cells)
      (hrsum : (r.re : Real) + (s.re : Real) + 1 = 2 * c.1)
      (hisum : (r.im : Real) + (s.im : Real) + 1 = 2 * c.2) :
      s ∈ O.cells := by
    apply (P3776T1CellCenterMembership O s).mp
    rw [show TileRealization O =
      (fun p : Real × Real => (2 * c.1 - p.1, 2 * c.2 - p.2)) ''
        TileRealization O from hsym]
    refine ⟨GaussianRealPoint r + ((1 / 2, 1 / 2) : Real × Real),
      (P3776T1CellCenterMembership O r).mpr hr, ?_⟩
    apply Prod.ext <;> dsimp [GaussianRealPoint] <;> linarith
  have heq : z ∈ O.cells ↔ w ∈ O.cells :=
    ⟨fun hz => image_center z w hz hsum.1 hsum.2,
      fun hw => image_center w z hw (by linarith [hsum.1]) (by linarith [hsum.2])⟩
  intro he
  rcases (hgeom O).2.1.mp he with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact hw (heq.mp hz)
  · exact hz (heq.mpr hw)

end ApollonianSuperharmonic

end
