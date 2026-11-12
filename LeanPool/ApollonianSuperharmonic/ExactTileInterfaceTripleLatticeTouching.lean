/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: ExactTileInterfaceTripleLatticeTouching]

/-!
# ExactTileInterfaceTripleLatticeTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ExactTileInterfaceTripleLatticeTouching
    (A B C : ProtoTile) (E : ExactTileInterfaceTriple A B C)
    (hA : LatticeTile A) (hB : LatticeTile B) (hC : LatticeTile C)
    (hAB : Disjoint A.cells B.cells)
    (hBC : Disjoint B.cells C.cells)
    (hCA : Disjoint C.cells A.cells) :
    TouchingTriple A B C := by
-- BODY
  have hneA : A.cells.Nonempty := (LatticeTileGridStructure A hA).1.1
  have hneB : B.cells.Nonempty := (LatticeTileGridStructure B hB).1.1
  have hneC : C.cells.Nonempty := (LatticeTileGridStructure C hC).1.1
  have between_to_path : ∀ (V : Set GaussianInt)
      (F : Set (Finset GaussianInt)) (x y : GaussianInt),
      SimpleGridPathBetween V F x y → SimpleGridPath V F := by
    intro V F x y h
    rcases h with ⟨p, hn, hlen, hhead, hlast, hvertices, hsteps, hedges⟩
    exact ⟨p, hn, hlen, hvertices, hsteps, hedges⟩
  have boundary_edge_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := by
    let I : GaussianInt := ⟨0, 1⟩
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - I, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [I, Zsqrtd.ext_iff]
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp []
  have edge_vertex_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices T := by
    rcases he with ⟨c, hc, he⟩
    unfold FootprintVertices
    rw [ite_eq_left ⟨c, hc⟩]
    rcases he with h | h | h | h <;> subst e
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    · rcases hz with rfl | rfl
      · exact ⟨_, hc, Or.inl rfl⟩
      · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
    · rcases hz with rfl | rfl
      · exact ⟨_, hc, Or.inl rfl⟩
      · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · rcases hz with rfl | rfl
      · exact ⟨_, hc, Or.inr (Or.inl rfl)⟩
      · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases hz with rfl | rfl
      · exact ⟨_, hc, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨_, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  have boundary_vertex_footprint (T : ProtoTile) (hne : T.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ BoundaryFootprintVertices T) :
      z ∈ FootprintVertices T := by
    unfold BoundaryFootprintVertices at hz
    rw [ite_eq_left hne] at hz
    rcases hz with ⟨e, he, hze⟩
    exact edge_vertex_footprint T e (boundary_edge_footprint T e he) z hze
  have boundary_vertex_of_edge (T : ProtoTile) (hne : T.cells.Nonempty)
      (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T)
      (z : GaussianInt) (hze : z ∈ e) :
      z ∈ BoundaryFootprintVertices T := by
    unfold BoundaryFootprintVertices
    rw [ite_eq_left hne]
    exact ⟨e, he, hze⟩
  have rawAB : SimpleGridPath
      (FootprintVertices A ∩ FootprintVertices B)
      (FootprintEdges A ∩ FootprintEdges B) :=
    between_to_path _ _ _ _ E.pathAB
  have rawBC : SimpleGridPath
      (FootprintVertices B ∩ FootprintVertices C)
      (FootprintEdges B ∩ FootprintEdges C) :=
    between_to_path _ _ _ _ E.pathBC
  have rawCA : SimpleGridPath
      (FootprintVertices C ∩ FootprintVertices A)
      (FootprintEdges C ∩ FootprintEdges A) :=
    between_to_path _ _ _ _ E.pathCA
  have edgesAB := CellDisjointCommonEdgesBoundary A B hAB
  have edgesBC := CellDisjointCommonEdgesBoundary B C hBC
  have edgesCA := CellDisjointCommonEdgesBoundary C A hCA
  have verticesAB : FootprintVertices A ∩ FootprintVertices B =
      BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases SimpleGridPathVertexIncidentEdge _ _ rawAB z hz with ⟨e, hze, he⟩
      have he' : e ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B :=
        edgesAB ▸ he
      exact ⟨boundary_vertex_of_edge A hneA e he'.1 z hze,
        boundary_vertex_of_edge B hneB e he'.2 z hze⟩
    · rintro z ⟨hzA, hzB⟩
      exact ⟨boundary_vertex_footprint A hneA z hzA,
        boundary_vertex_footprint B hneB z hzB⟩
  have verticesBC : FootprintVertices B ∩ FootprintVertices C =
      BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases SimpleGridPathVertexIncidentEdge _ _ rawBC z hz with ⟨e, hze, he⟩
      have he' : e ∈ BoundaryFootprintEdges B ∩ BoundaryFootprintEdges C :=
        edgesBC ▸ he
      exact ⟨boundary_vertex_of_edge B hneB e he'.1 z hze,
        boundary_vertex_of_edge C hneC e he'.2 z hze⟩
    · rintro z ⟨hzB, hzC⟩
      exact ⟨boundary_vertex_footprint B hneB z hzB,
        boundary_vertex_footprint C hneC z hzC⟩
  have verticesCA : FootprintVertices C ∩ FootprintVertices A =
      BoundaryFootprintVertices C ∩ BoundaryFootprintVertices A := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases SimpleGridPathVertexIncidentEdge _ _ rawCA z hz with ⟨e, hze, he⟩
      have he' : e ∈ BoundaryFootprintEdges C ∩ BoundaryFootprintEdges A :=
        edgesCA ▸ he
      exact ⟨boundary_vertex_of_edge C hneC e he'.1 z hze,
        boundary_vertex_of_edge A hneA e he'.2 z hze⟩
    · rintro z ⟨hzC, hzA⟩
      exact ⟨boundary_vertex_footprint C hneC z hzC,
        boundary_vertex_footprint A hneA z hzA⟩
  have pathAB : SimpleGridPath
      (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
      (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B) := by
    rw [← verticesAB, ← edgesAB]
    exact rawAB
  have pathBC : SimpleGridPath
      (BoundaryFootprintVertices B ∩ BoundaryFootprintVertices C)
      (BoundaryFootprintEdges B ∩ BoundaryFootprintEdges C) := by
    rw [← verticesBC, ← edgesBC]
    exact rawBC
  have pathCA : SimpleGridPath
      (BoundaryFootprintVertices C ∩ BoundaryFootprintVertices A)
      (BoundaryFootprintEdges C ∩ BoundaryFootprintEdges A) := by
    rw [← verticesCA, ← edgesCA]
    exact rawCA
  unfold TouchingTriple
  refine ⟨Or.inl ⟨hneA, hneB, hAB, pathAB⟩,
    Or.inl ⟨hneB, hneC, hBC, pathBC⟩,
    Or.inl ⟨hneC, hneA, hCA, pathCA⟩, E.point, ?_, ?_⟩
  · have hp := (E.unique_common E.point).mpr rfl
    have hpAB : E.point ∈ BoundaryFootprintVertices A ∩
        BoundaryFootprintVertices B := verticesAB ▸ hp.1
    have hpBC : E.point ∈ BoundaryFootprintVertices B ∩
        BoundaryFootprintVertices C := verticesBC ▸ ⟨hp.1.2, hp.2⟩
    exact ⟨hpAB.1, hpAB.2, hpBC.2⟩
  · intro z hz
    apply (E.unique_common z).mp
    have hzAB : z ∈ FootprintVertices A ∩ FootprintVertices B :=
      verticesAB.symm ▸ ⟨hz.1, hz.2.1⟩
    have hzBC : z ∈ FootprintVertices B ∩ FootprintVertices C :=
      verticesBC.symm ▸ ⟨hz.2.1, hz.2.2⟩
    exact ⟨hzAB, hzBC.2⟩

end ApollonianSuperharmonic

end
