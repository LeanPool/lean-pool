/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4456T2VertexInterior
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.P4397T1UnitEdgeCells
public import LeanPool.ApollonianSuperharmonic.P4456T2EdgeInterior
public import LeanPool.ApollonianSuperharmonic.LatticeTileFourNeighborConnected

-- [TABLET NODE: P4456T2ParentSide]

/-!
# P4456T2ParentSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4456T2ParentSide (T U : ProtoTile)
    (hT : LatticeTile T) (hU : LatticeTile U) (hsub : U.cells ⊆ T.cells)
    (x y : GaussianInt) (hxy : FourNeighborAdjacent x y)
    (hx : x ∈ BoundaryFootprintVertices T)
    (hy : y ∈ BoundaryFootprintVertices T)
    (side : GaussianInt → Int)
    (hstep : ∀ c ∈ T.cells, ∀ d ∈ T.cells, c ≠ d →
      ∀ f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) ∩
        FootprintEdges (⟨{d}, d⟩ : ProtoTile), side c ≠ side d → f = {x, y})
    (hnochord : ∀ u v, FourNeighborAdjacent u v →
      u ∈ BoundaryFootprintVertices U → v ∈ BoundaryFootprintVertices U →
      ¬ OpenLatticeEdge u v ⊆ interior (TileRealization U)) :
    ∃ k : Int, ∀ c ∈ U.cells, side c = k := by
-- BODY
  classical
  have hneT : T.cells.Nonempty := (LatticeTileFourNeighborConnected T hT).1
  have hneU : U.cells.Nonempty := (LatticeTileFourNeighborConnected U hU).1
  have adjacent_equal : ∀ c ∈ U.cells, ∀ d ∈ U.cells,
      FourNeighborAdjacent c d → side c = side d := by
    intro c hc d hd hcd
    have hct : c ∈ T.cells := hsub hc
    have hdt : d ∈ T.cells := hsub hd
    have hne : c ≠ d := by
      intro h
      subst d
      rcases hcd with h | h | h | h <;> simp [Zsqrtd.ext_iff] at h <;> omega
    have change_impossible (f : Finset GaussianInt)
        (hfc : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile))
        (hfd : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile))
        (hfeq : f = {x, y}) (hlabels : side c ≠ side d) : False := by
      have hf : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) ∩
          FootprintEdges (⟨{d}, d⟩ : ProtoTile) := ⟨hfc, hfd⟩
      have hab : {x, y} ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
        rw [← hfeq]
        exact hfc
      have habD : {x, y} ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
        rw [← hfeq]
        exact hfd
      have hcdedge : OpenLatticeEdge x y ⊆ interior (TileRealization U) := by
        exact (P4456T2EdgeInterior U x y c d hxy hne hab habD).2 ⟨hc, hd⟩
      rcases P4397T1UnitEdgeCells.1 x y hxy with ⟨z, w, hform⟩
      have unitU := P4397T1UnitEdgeCells.2 x y z w hform U
      have hoccU : z ∈ U.cells ∨ w ∈ U.cells := by
        have unitC := P4397T1UnitEdgeCells.2 x y z w hform (⟨{c}, c⟩ : ProtoTile)
        have hoccC : z ∈ ({c} : Finset GaussianInt) ∨ w ∈ ({c} : Finset GaussianInt) :=
          unitC.1.mp hab
        rcases hoccC with hz | hw
        · have : z = c := Finset.mem_singleton.mp hz
          subst z
          exact Or.inl hc
        · have : w = c := Finset.mem_singleton.mp hw
          subst w
          exact Or.inr hc
      have hvertices := unitU.2.2.1 hoccU
      have hxUfoot : x ∈ FootprintVertices U := hvertices.1
      have hyUfoot : y ∈ FootprintVertices U := hvertices.2.1
      have hxTfoot : x ∈ FootprintVertices T := by
        simp only [FootprintVertices, ite_eq_left hneU] at hxUfoot
        simp only [FootprintVertices, ite_eq_left hneT]
        rcases hxUfoot with ⟨q, hq, hcorner⟩
        exact ⟨q, hsub hq, hcorner⟩
      have hyTfoot : y ∈ FootprintVertices T := by
        simp only [FootprintVertices, ite_eq_left hneU] at hyUfoot
        simp only [FootprintVertices, ite_eq_left hneT]
        rcases hyUfoot with ⟨q, hq, hcorner⟩
        exact ⟨q, hsub hq, hcorner⟩
      have hxU : x ∈ BoundaryFootprintVertices U := by
        have hnotall : ¬ ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells := by
          intro hall
          have hallT : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells :=
            fun j => hsub (hall j)
          have hxnot : x ∉ BoundaryFootprintVertices T :=
            (P4456T2VertexInterior T hneT x hxTfoot).2.mpr hallT
          exact hxnot hx
        by_contra hbound
        exact hnotall ((P4456T2VertexInterior U hneU x hxUfoot).2.mp hbound)
      have hyU : y ∈ BoundaryFootprintVertices U := by
        have hnotall : ¬ ∀ j : Fin 4, LatticeVertexIncidentCell y j ∈ U.cells := by
          intro hall
          have hallT : ∀ j : Fin 4, LatticeVertexIncidentCell y j ∈ T.cells :=
            fun j => hsub (hall j)
          have hynot : y ∉ BoundaryFootprintVertices T :=
            (P4456T2VertexInterior T hneT y hyTfoot).2.mpr hallT
          exact hynot hy
        by_contra hbound
        exact hnotall ((P4456T2VertexInterior U hneU y hyUfoot).2.mp hbound)
      exact hnochord x y hxy hxU hyU hcdedge
    change d = c + 1 ∨ d = c - 1 ∨ d = c + ⟨0, 1⟩ ∨ d = c - ⟨0, 1⟩ at hcd
    rcases hcd with hdir | hdir | hdir | hdir
    · let f : Finset GaussianInt := {c + 1, c + 1 + ⟨0, 1⟩}
      have hfc : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
        simp [f, FootprintEdges, add_assoc]
      have hfd : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
        subst d
        simp [f, FootprintEdges, add_assoc, add_comm, add_left_comm]
      by_cases hlabels : side c = side d
      · exact hlabels
      · have hfeq : f = {x, y} := by
          apply hstep c hct d hdt hne f ⟨hfc, hfd⟩ hlabels
        exact False.elim (change_impossible f hfc hfd hfeq hlabels)
    · let f : Finset GaussianInt := {c, c + ⟨0, 1⟩}
      have hfc : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
        simp [f, FootprintEdges]
      have hfd : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
        subst d
        simp [f, FootprintEdges, sub_eq_add_neg, add_assoc]
      by_cases hlabels : side c = side d
      · exact hlabels
      · have hfeq : f = {x, y} := by
          apply hstep c hct d hdt hne f ⟨hfc, hfd⟩ hlabels
        exact False.elim (change_impossible f hfc hfd hfeq hlabels)
    · let f : Finset GaussianInt := {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}
      have hfc : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
        simp [f, FootprintEdges, add_assoc]
      have hfd : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
        subst d
        simp [f, FootprintEdges, add_assoc, add_comm, add_left_comm]
      by_cases hlabels : side c = side d
      · exact hlabels
      · have hfeq : f = {x, y} := by
          apply hstep c hct d hdt hne f ⟨hfc, hfd⟩ hlabels
        exact False.elim (change_impossible f hfc hfd hfeq hlabels)
    · let f : Finset GaussianInt := {c, c + 1}
      have hfc : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) := by
        simp [f, FootprintEdges]
      have hfd : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) := by
        subst d
        simp [f, FootprintEdges, sub_eq_add_neg, add_assoc]
      by_cases hlabels : side c = side d
      · exact hlabels
      · have hfeq : f = {x, y} := by
          apply hstep c hct d hdt hne f ⟨hfc, hfd⟩ hlabels
        exact False.elim (change_impossible f hfc hfd hfeq hlabels)
  obtain ⟨c₀, hc₀⟩ := hneU
  refine ⟨side c₀, ?_⟩
  intro c hc
  obtain ⟨p, hphead, hplast, hpinside, hpadj⟩ :=
    (LatticeTileFourNeighborConnected U hU).2 c₀ hc₀ c hc
  have hchain : List.IsChain FourNeighborAdjacent p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    exact hpadj
  have hlabels : List.IsChain (fun a b => side a = side b) p :=
    hchain.imp_of_mem_imp (fun a b ha hb hab =>
      adjacent_equal a (hpinside a ha) b (hpinside b hb) hab)
  cases p with
  | nil => simp at hphead
  | cons a p =>
    have hac : a = c₀ := by simpa using Option.some.inj hphead
    subst a
    have hcmem : c ∈ c₀ :: p := by
      rcases List.getLast?_eq_some_iff.mp hplast with ⟨l, hl⟩
      rw [hl]
      simp
    simp only [List.mem_cons] at hcmem
    rcases hcmem with hcc | hcp
    · simp [hcc]
    · exact (hlabels.rel_cons hcp).symm

end ApollonianSuperharmonic

end
