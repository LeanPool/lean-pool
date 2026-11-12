/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.ConnectedGridEdgeCarrierUnion
public import LeanPool.ApollonianSuperharmonic.DisjointBoundaryCommonEdgeGraphAcyclic
public import LeanPool.ApollonianSuperharmonic.DisjointSquareUnionCommonEdgeCarrier
public import LeanPool.ApollonianSuperharmonic.FiniteAcyclicGraphCardConnected
public import LeanPool.ApollonianSuperharmonic.FiniteGridEdgeGraphEncoding
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridEulerCount
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.TileRealization

-- [TABLET NODE: LatticeDiskUnionIntersectionConnected]

/-!
# LatticeDiskUnionIntersectionConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LatticeDiskUnionIntersectionConnected (U V W : ProtoTile)
    (hU : LatticeTile U) (hV : LatticeTile V) (hW : LatticeTile W)
    (hdisjoint : Disjoint U.cells V.cells)
    (hunion : ∀ z : LatticeCell,
      z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells)
    (hcommon :
      (FootprintEdges U ∩ FootprintEdges V).Nonempty) :
    IsConnected (TileRealization U ∩ TileRealization V) := by
-- BODY
  classical
  let X : Set GaussianInt := FootprintVertices U ∩ FootprintVertices V
  let E : Set (Finset GaussianInt) := FootprintEdges U ∩ FootprintEdges V
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ E
  have hUne : U.cells.Nonempty := (LatticeTileGridStructure U hU).1.1
  have hVne : V.cells.Nonempty := (LatticeTileGridStructure V hV).1.1
  have hWne : W.cells.Nonempty := (LatticeTileGridStructure W hW).1.1
  have hvertices : FootprintVertices W =
      FootprintVertices U ∪ FootprintVertices V := by
    simp only [FootprintVertices, hUne, hVne, hWne, ite_true]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨x, hx, hz⟩
      rw [hunion x] at hx
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hx, hz⟩
      · exact Or.inr ⟨x, hx, hz⟩
    · rintro (⟨x, hx, hz⟩ | ⟨x, hx, hz⟩)
      · exact ⟨x, (hunion x).2 (Or.inl hx), hz⟩
      · exact ⟨x, (hunion x).2 (Or.inr hx), hz⟩
  have hedges : FootprintEdges W = FootprintEdges U ∪ FootprintEdges V := by
    ext e
    simp only [FootprintEdges, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨x, hx, he⟩
      rw [hunion x] at hx
      exact hx.elim (fun h => Or.inl ⟨x, h, he⟩)
        (fun h => Or.inr ⟨x, h, he⟩)
    · rintro (⟨x, hx, he⟩ | ⟨x, hx, he⟩)
      · exact ⟨x, (hunion x).2 (Or.inl hx), he⟩
      · exact ⟨x, (hunion x).2 (Or.inr hx), he⟩
  have vertex_finite (T : ProtoTile) : (FootprintVertices T).Finite := by
    simp only [FootprintVertices]
    split_ifs
    · let corner : T.cells × (Bool × Bool) → GaussianInt := fun q =>
        match q.2 with
        | (false, false) => q.1.1
        | (false, true) => q.1.1 + 1
        | (true, false) => q.1.1 + ⟨0, 1⟩
        | (true, true) => q.1.1 + 1 + ⟨0, 1⟩
      apply (Set.finite_range corner).subset
      rintro z ⟨x, hx, hz⟩
      rcases hz with hz | hz | hz | hz
      · exact ⟨(⟨x, hx⟩, false, false), by simpa [corner] using hz.symm⟩
      · exact ⟨(⟨x, hx⟩, false, true), by simpa [corner] using hz.symm⟩
      · exact ⟨(⟨x, hx⟩, true, false), by simpa [corner] using hz.symm⟩
      · exact ⟨(⟨x, hx⟩, true, true), by simpa [corner] using hz.symm⟩
    · exact Set.finite_singleton T.anchor
  have edge_finite (T : ProtoTile) : (FootprintEdges T).Finite := by
    let edge : T.cells × (Bool × Bool) → Finset GaussianInt := fun q =>
      match q.2 with
      | (false, false) => {q.1.1, q.1.1 + 1}
      | (false, true) => {q.1.1, q.1.1 + ⟨0, 1⟩}
      | (true, false) => {q.1.1 + 1, q.1.1 + 1 + ⟨0, 1⟩}
      | (true, true) => {q.1.1 + ⟨0, 1⟩, q.1.1 + 1 + ⟨0, 1⟩}
    apply (Set.finite_range edge).subset
    rintro e ⟨c, hc, h | h | h | h⟩
    · exact ⟨(⟨c, hc⟩, false, false), by simpa [edge] using h.symm⟩
    · exact ⟨(⟨c, hc⟩, false, true), by simpa [edge] using h.symm⟩
    · exact ⟨(⟨c, hc⟩, true, false), by simpa [edge] using h.symm⟩
    · exact ⟨(⟨c, hc⟩, true, true), by simpa [edge] using h.symm⟩
  have hvertexIE := Set.ncard_union_add_ncard_inter
    (FootprintVertices U) (FootprintVertices V) (vertex_finite U) (vertex_finite V)
  have hedgeIE := Set.ncard_union_add_ncard_inter
    (FootprintEdges U) (FootprintEdges V) (edge_finite U) (edge_finite V)
  have hcellcard : W.cells.card = U.cells.card + V.cells.card := by
    have hfin : W.cells = U.cells ∪ V.cells := by
      ext z
      simpa using hunion z
    rw [hfin, Finset.card_union_of_disjoint hdisjoint]
  have hEulerU := LatticeTileGridEulerCount U hU
  have hEulerV := LatticeTileGridEulerCount V hV
  have hEulerW := LatticeTileGridEulerCount W hW
  have hcount : X.ncard = E.ncard + 1 := by
    dsimp [X, E]
    rw [← hvertices] at hvertexIE
    rw [← hedges] at hedgeIE
    omega
  have hEfinite : E.Finite := (edge_finite U).inter_of_left (FootprintEdges V)
  have hXfinite : X.Finite := (vertex_finite U).inter_of_left (FootprintVertices V)
  have hgrid : ∀ e ∈ E, ∃ a b : GaussianInt,
      e = {a, b} ∧ FourNeighborAdjacent a b := by
    intro e he
    rcases he.1 with ⟨x, hx, rfl | rfl | rfl | rfl⟩
    · exact ⟨x, x + 1, rfl, Or.inl rfl⟩
    · exact ⟨x, x + ⟨0, 1⟩, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨x + 1, x + 1 + ⟨0, 1⟩, rfl,
        Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩, rfl, Or.inl (by ring)⟩
  have hendpoint : {x | ∃ e ∈ E, x ∈ e} ⊆ X := by
    rintro x ⟨e, he, hxe⟩
    have endpoint_mem (T : ProtoTile) (hne : T.cells.Nonempty)
        (heT : e ∈ FootprintEdges T) : x ∈ FootprintVertices T := by
      simp only [FootprintVertices, hne, ite_true]
      rcases heT with ⟨c, hc, hec⟩
      refine ⟨c, hc, ?_⟩
      rcases hec with hec | hec | hec | hec
      all_goals rw [hec] at hxe
      all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      · exact hxe.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact hxe.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
      · exact hxe.elim (fun h => Or.inr (Or.inl h))
          (fun h => Or.inr (Or.inr (Or.inr h)))
      · exact hxe.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          (fun h => Or.inr (Or.inr (Or.inr h)))
    exact ⟨endpoint_mem U hUne he.1, endpoint_mem V hVne he.2⟩
  have hboundary := CellDisjointCommonEdgesBoundary U V hdisjoint
  have hacyclicSmall := DisjointBoundaryCommonEdgeGraphAcyclic U V hdisjoint
    (LatticeTileGridStructure U hU).2.2
    (LatticeTileGridStructure V hV).2.2 hcommon hboundary
  have hencoding := FiniteGridEdgeGraphEncoding X E
    hgrid hendpoint hacyclicSmall
  have hXnonempty : X.Nonempty := by
    rcases hcommon with ⟨e, he⟩
    rcases hgrid e he with ⟨a, b, rfl, hab⟩
    exact ⟨a, hendpoint ⟨{a, b}, by simpa, by simp⟩⟩
  let : Nonempty X := Set.nonempty_coe_sort.mpr hXnonempty
  let : Fintype X := hXfinite.fintype
  have hGconnected : G.Connected := by
    apply FiniteAcyclicGraphCardConnected G hencoding.1
    rw [hencoding.2]
    simpa [X] using hcount
  have hsupport : X = {x | ∃ e ∈ E, x ∈ e} := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hcommon with ⟨e, he⟩
      rcases hgrid e he with ⟨a, b, hab, hadj⟩
      have habE : ({a, b} : Finset GaussianInt) ∈ E := hab ▸ he
      have haX : a ∈ X := hendpoint ⟨{a, b}, habE, by simp⟩
      by_cases hxa : x = a
      · subst x
        exact ⟨{a, b}, habE, by simp⟩
      · have hreach : G.Reachable ⟨x, hx⟩ ⟨a, haX⟩ :=
          hGconnected.preconnected _ _
        rcases hreach.nonempty_neighborSet_left (Subtype.ext_iff.not.mpr hxa) with
          ⟨y, hxy⟩
        have hxy' : ({x, y.1} : Finset GaussianInt) ∈ E := by
          change (⟨x, hx⟩ : X) ≠ y ∧
            (({x, y.1} : Finset GaussianInt) ∈ E ∨
              ({y.1, x} : Finset GaussianInt) ∈ E) at hxy
          exact hxy.2.elim id (by simp [Finset.pair_comm])
        exact ⟨{x, y.1}, hxy', by simp⟩
    · exact hendpoint
  have hcarrier := DisjointSquareUnionCommonEdgeCarrier U V hdisjoint (by
    change X = CommonFootprintEdgeVertices U V
    simpa only [CommonFootprintEdgeVertices, E] using hsupport)
  rw [hcarrier.2]
  exact ConnectedGridEdgeCarrierUnion X E hcommon hgrid
    hsupport hGconnected

end ApollonianSuperharmonic

end
