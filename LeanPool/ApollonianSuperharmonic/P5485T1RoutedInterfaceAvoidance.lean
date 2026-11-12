/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceData
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.OppositeRoutedCommonEdgeOutsideCellUnique
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P5485T1RoutedInterfaceAvoidance]

/-!
# P5485T1RoutedInterfaceAvoidance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5485T1RoutedInterfaceAvoidance
    (V W G H K : ProtoTile)
    (data : P4418T3SelectedInterfaceData V W G H)
    (hK : K.cells.Nonempty)
    (hVK : Disjoint V.cells K.cells) (hWK : Disjoint W.cells K.cells)
    (hGK : Disjoint G.cells K.cells) (hHK : Disjoint H.cells K.cells)
    (x : GaussianInt) (j : Fin 4) (edge : Finset GaussianInt)
    (hx : x ∈ edge)
    (hedge : edge ∈ FootprintEdges V ∩ FootprintEdges W)
    (hV : LatticeVertexIncidentCell x j ∈ V.cells)
    (hW : LatticeVertexIncidentCell x (j + 2) ∈ W.cells) :
    x ∉ FootprintVertices K := by
-- BODY
  intro hfoot
  have incident (U : ProtoTile) (hne : U.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices U) :
      ∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells := by
    simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨c, hc, rfl | rfl | rfl | rfl⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using hc⟩
  obtain ⟨k, hk⟩ := incident K hK x hfoot
  have outsideV : LatticeVertexIncidentCell x k ∉ V.cells :=
    fun hc => Finset.disjoint_left.mp hVK hc hk
  have outsideW : LatticeVertexIncidentCell x k ∉ W.cells :=
    fun hc => Finset.disjoint_left.mp hWK hc hk
  have endpoint (Z : ProtoTile) (hZ : LatticeTile Z)
      (hVZ : Disjoint V.cells Z.cells) (hWZ : Disjoint W.cells Z.cells)
      (hZK : Disjoint Z.cells K.cells) (hz : x ∈ FootprintVertices Z) : False := by
    obtain ⟨l, hl⟩ := incident Z (LatticeTileGridStructure Z hZ).1.1 x hz
    have heq := OppositeRoutedCommonEdgeOutsideCellUnique V W x j edge
      data.disjointVW hx hedge hV hW l k
      (fun hc => Finset.disjoint_left.mp hVZ hc hl)
      (fun hc => Finset.disjoint_left.mp hWZ hc hl) outsideV outsideW
    exact Finset.disjoint_left.mp hZK hl (heq.symm ▸ hk)
  rcases SimpleGridPathPointTrichotomy _ _ data.first data.last x
      data.path ⟨edge, hx, hedge⟩ with hfirst | hlast | hinterior
  · exact endpoint G data.latticeG₀ data.disjointVG₀ data.disjointWG₀
      hGK (hfirst.symm ▸ data.common₀.2)
  · exact endpoint H data.latticeG₁ data.disjointVG₁ data.disjointWG₁
      hHK (hlast.symm ▸ data.common₁.2)
  · rcases (LocalLatticeInterfaceSectors.2 V W x data.latticeV
      data.latticeW data.disjointVW hinterior).1 k with hv | hw
    · exact outsideV hv
    · exact outsideW hw

end ApollonianSuperharmonic

end
