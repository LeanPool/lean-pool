/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.P4397T1UnitEdgeCells

-- [TABLET NODE: P4651T1ContactEdgeSeparation]

/-!
# P4651T1ContactEdgeSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4651T1ContactEdgeSeparation (Dplus Dminus O : ProtoTile)
    (hp : Disjoint Dplus.cells O.cells)
    (hm : Disjoint Dminus.cells O.cells)
    (hpm : Disjoint Dplus.cells Dminus.cells) :
    (∀ S : ProtoTile, S.cells ⊆ Dplus.cells →
      BoundaryFootprintEdges S ∩ BoundaryFootprintEdges O ⊆
        BoundaryFootprintEdges Dplus ∩ BoundaryFootprintEdges O) ∧
    (∀ S : ProtoTile, S.cells ⊆ Dminus.cells →
      BoundaryFootprintEdges S ∩ BoundaryFootprintEdges O ⊆
        BoundaryFootprintEdges Dminus ∩ BoundaryFootprintEdges O) ∧
    Disjoint (BoundaryFootprintEdges Dplus ∩ BoundaryFootprintEdges O)
      (BoundaryFootprintEdges Dminus ∩ BoundaryFootprintEdges O) := by
-- BODY
  classical
  have grow (D S : ProtoTile) (hd : Disjoint D.cells O.cells)
      (hsub : S.cells ⊆ D.cells) :
      BoundaryFootprintEdges S ∩ BoundaryFootprintEdges O ⊆
        BoundaryFootprintEdges D ∩ BoundaryFootprintEdges O := by
    have hs : Disjoint S.cells O.cells := Finset.disjoint_left.mpr
      (fun _ hx hy => Finset.disjoint_left.mp hd (hsub hx) hy)
    rw [← CellDisjointCommonEdgesBoundary S O hs,
      ← CellDisjointCommonEdgesBoundary D O hd]
    rintro e ⟨⟨x, hx, hshape⟩, he⟩
    exact ⟨⟨x, hsub hx, hshape⟩, he⟩
  refine ⟨fun S hS => grow Dplus S hp hS,
    fun S hS => grow Dminus S hm hS, ?_⟩
  apply Set.disjoint_left.mpr
  rintro e ⟨hep, heO⟩ ⟨hem, _⟩
  have impossible (a b : GaussianInt) (hadj : FourNeighborAdjacent a b)
      (hpE : {a, b} ∈ BoundaryFootprintEdges Dplus)
      (hmE : {a, b} ∈ BoundaryFootprintEdges Dminus)
      (hOE : {a, b} ∈ BoundaryFootprintEdges O) : False := by
    obtain ⟨z, w, hshape⟩ := P4397T1UnitEdgeCells.1 a b hadj
    have hP := (P4397T1UnitEdgeCells.2 a b z w hshape Dplus).2.1.mp hpE
    have hM := (P4397T1UnitEdgeCells.2 a b z w hshape Dminus).2.1.mp hmE
    have hO := (P4397T1UnitEdgeCells.2 a b z w hshape O).2.1.mp hOE
    have hpo := Finset.disjoint_left.mp hp
    have hmo := Finset.disjoint_left.mp hm
    have hpm' := Finset.disjoint_left.mp hpm
    rcases hP with ⟨hzp, _⟩ | ⟨_, hwp⟩ <;>
      rcases hM with ⟨hzm, _⟩ | ⟨_, hwm⟩ <;>
      rcases hO with ⟨hzo, _⟩ | ⟨_, hwo⟩
    all_goals first | exact hpo hzp hzo | exact hpo hwp hwo |
      exact hmo hzm hzo | exact hmo hwm hwo |
      exact hpm' hzp hzm | exact hpm' hwp hwm
  obtain ⟨z, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := heO
  · exact impossible z (z + 1) (Or.inl rfl) hep hem
      ⟨z, Or.inl ⟨rfl, by assumption⟩⟩
  · exact impossible z (z + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl))) hep hem
      ⟨z, Or.inr ⟨rfl, by assumption⟩⟩

end ApollonianSuperharmonic

end
