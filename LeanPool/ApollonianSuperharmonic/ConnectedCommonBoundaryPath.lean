/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.ConnectedGridEdgeCarrierGraph
public import LeanPool.ApollonianSuperharmonic.DisjointBoundaryCommonEdgeGraphAcyclic
public import LeanPool.ApollonianSuperharmonic.DisjointSquareUnionCommonEdgeCarrier
public import LeanPool.ApollonianSuperharmonic.FiniteConnectedAcyclicDegreeTwoGridPath
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycleSubgraphDegreeTwo
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: ConnectedCommonBoundaryPath]

/-!
# ConnectedCommonBoundaryPath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ConnectedCommonBoundaryPath (U V : ProtoTile)
    (hUne : U.cells.Nonempty) (hVne : V.cells.Nonempty)
    (hdisjoint : Disjoint U.cells V.cells)
    (hconnected : IsConnected
      (TileRealization U ∩ TileRealization V))
    (hUcycle : SimpleGridCycle (BoundaryFootprintVertices U)
      (BoundaryFootprintEdges U))
    (hVcycle : SimpleGridCycle (BoundaryFootprintVertices V)
      (BoundaryFootprintEdges V))
    (hcommon :
      (FootprintEdges U ∩ FootprintEdges V).Nonempty) :
    ∃ x y : GaussianInt,
      SimpleGridPathBetween
        (CommonFootprintEdgeVertices U V)
        (FootprintEdges U ∩ FootprintEdges V) x y := by
-- BODY
  classical
  obtain ⟨hedges, hvertices, hboundaryVertices⟩ :=
    CellDisjointCommonFootprintIncidence U V hUne hVne hdisjoint
      hconnected hcommon
  obtain ⟨hEfinite, hcarrier⟩ :=
    DisjointSquareUnionCommonEdgeCarrier U V hdisjoint hvertices
  let E : Set (Finset GaussianInt) := FootprintEdges U ∩ FootprintEdges V
  let X : Set GaussianInt := CommonFootprintEdgeVertices U V
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  have hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b := by
    intro e he
    rcases he.1 with ⟨c, hc, he | he | he | he⟩
    · exact ⟨c, c + 1, he, Or.inl rfl⟩
    · exact ⟨c, c + ⟨0, 1⟩, he, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨c + 1, c + 1 + ⟨0, 1⟩, he,
        Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩, he, Or.inl (by
        apply Zsqrtd.ext <;> simp)⟩
  have hgraphConnected : G.Connected := by
    apply ConnectedGridEdgeCarrierGraph E hEfinite hgrid
    simpa [E] using hcarrier ▸ hconnected
  have hXU : X ⊆ BoundaryFootprintVertices U := by
    intro x hx
    have hx' : x ∈ CommonFootprintEdgeVertices U V := hx
    have hx'' : x ∈ BoundaryFootprintVertices U ∩
        BoundaryFootprintVertices V := by
      rw [hboundaryVertices]
      exact hx'
    exact hx''.1
  have hEU : E ⊆ BoundaryFootprintEdges U := by
    intro e he
    have : e ∈ BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V :=
      hedges ▸ he
    exact this.1
  have hendpoints : X = {x | ∃ e ∈ E, x ∈ e} := by
    rfl
  have hdegree : ∀ v : X, Set.ncard (G.neighborSet v) ≤ 2 := by
    exact SimpleGridCycleSubgraphDegreeTwo X (BoundaryFootprintVertices U)
      E (BoundaryFootprintEdges U) hUcycle hXU hEU
  have hacyclic : G.IsAcyclic := by
    exact DisjointBoundaryCommonEdgeGraphAcyclic U V hdisjoint hUcycle hVcycle
      hcommon hedges
  exact FiniteConnectedAcyclicDegreeTwoGridPath X E hEfinite hcommon
    hendpoints hgrid hgraphConnected hacyclic hdegree

end ApollonianSuperharmonic

end
