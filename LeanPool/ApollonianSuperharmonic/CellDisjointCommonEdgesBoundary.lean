/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCellEdges

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: CellDisjointCommonEdgesBoundary]

/-!
# CellDisjointCommonEdgesBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CellDisjointCommonEdgesBoundary (U V : ProtoTile)
    (hdisjoint : Disjoint U.cells V.cells) :
    FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
-- BODY
  classical
  let I : GaussianInt := ⟨0, 1⟩
  have footprint_normalize (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) :
      (∃ z, e = {z, z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨
      (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈ T.cells)) := by
    rcases he with ⟨x, hx, h | h | h | h⟩
    · exact Or.inl ⟨x, h, Or.inl hx⟩
    · exact Or.inr ⟨x, h, Or.inl hx⟩
    · refine Or.inr ⟨x + 1, h, Or.inr ?_⟩
      simpa [add_sub_cancel_right] using hx
    · refine Or.inl ⟨x + I, ?_, Or.inr ?_⟩
      · simpa [I, Zsqrtd.ext_iff, add_comm, add_left_comm, add_assoc] using h
      simpa [I, Zsqrtd.ext_iff] using hx
  have boundary_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := by
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [I, Zsqrtd.ext_iff]
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp
  ext e
  constructor
  · rintro ⟨heU, heV⟩
    have hd := Finset.disjoint_left.mp hdisjoint
    rcases footprint_normalize U e heU with ⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩ <;>
      rcases footprint_normalize V e heV with ⟨w, hw, hwV⟩ | ⟨w, hw, hwV⟩
    · have bzw : z = w := LatticeCellEdges.horizontal_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inl ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
    · exact (LatticeCellEdges.horizontal_ne_vertical z w (hz.symm.trans hw)).elim
    · exact (LatticeCellEdges.horizontal_ne_vertical w z (hw.symm.trans hz)).elim
    · have bzw : z = w := LatticeCellEdges.vertical_unique z w (hz.symm.trans hw)
      subst w
      constructor <;> refine ⟨z, Or.inr ⟨?_, ?_⟩⟩
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inl ⟨hzU, fun hbad => hd hbad hzV⟩
        · exact Or.inr ⟨fun hbad => hd hbad hzV, hzU⟩
        · exact (hd hzU hzV).elim
      · exact hz
      · rcases hzU with hzU | hzU <;> rcases hwV with hzV | hzV
        · exact (hd hzU hzV).elim
        · exact Or.inr ⟨fun hbad => hd hzU hbad, hzV⟩
        · exact Or.inl ⟨hzV, fun hbad => hd hzU hbad⟩
        · exact (hd hzU hzV).elim
  · rintro ⟨heU, heV⟩
    exact ⟨boundary_footprint U e heU, boundary_footprint V e heV⟩

end ApollonianSuperharmonic

end
