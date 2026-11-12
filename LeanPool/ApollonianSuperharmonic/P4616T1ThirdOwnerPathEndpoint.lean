/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy

-- [TABLET NODE: P4616T1ThirdOwnerPathEndpoint]

/-!
# P4616T1ThirdOwnerPathEndpoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4616T1ThirdOwnerPathEndpoint (U V W : ProtoTile)
    (p q vertex : GaussianInt) (vertices : Set GaussianInt)
    (hU : LatticeTile U) (hV : LatticeTile V)
    (hdis : Disjoint U.cells V.cells)
    (hpath : SimpleGridPathBetween vertices
      (FootprintEdges U ∩ FootprintEdges V) p q)
    (hxv : vertex ∈ vertices)
    (hthird : ∃ j : Fin 4,
      LatticeVertexIncidentCell vertex j ∈ W.cells ∧
        LatticeVertexIncidentCell vertex j ∉ U.cells ∧
        LatticeVertexIncidentCell vertex j ∉ V.cells) :
    vertex = p ∨ vertex = q := by
-- BODY
  have hsimple : SimpleGridPath vertices (FootprintEdges U ∩ FootprintEdges V) := by
    obtain ⟨l, hn, hl, _, _, hv, hs, he⟩ := hpath
    exact ⟨l, hn, hl, hv, hs, he⟩
  obtain h | h | h := SimpleGridPathPointTrichotomy _ _ p q vertex hpath
    (SimpleGridPathVertexIncidentEdge _ _ hsimple vertex hxv)
  · exact Or.inl h
  · exact Or.inr h
  · have hcover := (LocalLatticeInterfaceSectors.2 U V vertex hU hV hdis h).1
    obtain ⟨j, _, hju, hjv⟩ := hthird
    exact (hcover j).elim (fun hu => (hju hu).elim) (fun hv => (hjv hv).elim)

end ApollonianSuperharmonic

end
