/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FootprintFiniteness

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FiniteCycleComponentList
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: P5620T1BoundaryComponentCycle]

/-!
# P5620T1BoundaryComponentCycle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundaryComponentCycle

private noncomputable def BV (T : ProtoTile) := {v : GaussianInt // v ∈ BoundaryFootprintVertices T}

private noncomputable def G (T : ProtoTile) : SimpleGraph (BV T) := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T

private theorem boundary_edge_card_two (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e.card = 2 := by
  classical
  rcases he with ⟨z, (⟨rfl, hz⟩ | ⟨rfl, hz⟩)⟩
  · simp []
  · simp [Zsqrtd.ext_iff]

private theorem graph_adj_iff (T : ProtoTile) (a b : (BV T)) :
      (G T).Adj a b ↔
        a ≠ b ∧ ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
  classical
  let BV := {v : GaussianInt // v ∈ BoundaryFootprintVertices T}
  let G : SimpleGraph BV := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  change (G.Adj a b ↔
        a ≠ b ∧ ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T)
  simp only [G]
  constructor
  · rintro ⟨hne, hab | hba⟩
    · exact ⟨hne, hab⟩
    · refine ⟨hne, ?_⟩
      rw [Finset.pair_comm]
      exact hba
  · rintro ⟨hne, hab⟩
    exact ⟨hne, Or.inl hab⟩

private theorem graph_isCycles (T : ProtoTile) (cells_nonempty : T.cells.Nonempty)
    (boundary_degree_two : ∀ v ∈ BoundaryFootprintVertices T, Set.ncard {e : Finset GaussianInt |
    e ∈ BoundaryFootprintEdges T ∧ v ∈ e} = 2) : (G T).IsCycles := by
  classical
  let BV := {v : GaussianInt // v ∈ BoundaryFootprintVertices T}
  let G : SimpleGraph BV := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have boundary_edge_card_two (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e.card = 2 := boundary_edge_card_two T e he
  have graph_adj_iff (a b : BV) :
      G.Adj a b ↔
        a ≠ b ∧ ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := graph_adj_iff T a b
  change (G.IsCycles)
  intro v hn
  calc
    (G.neighborSet v).ncard =
        {e : Finset GaussianInt |
          e ∈ BoundaryFootprintEdges T ∧ v.1 ∈ e}.ncard := by
      apply Set.ncard_congr
          (fun w (_ : w ∈ G.neighborSet v) => ({v.1, w.1} : Finset GaussianInt))
      · intro w hw
        rw [SimpleGraph.mem_neighborSet] at hw
        have hadj := hw
        exact ⟨(graph_adj_iff v w).mp hadj |>.2, by simp⟩
      · intro a b ha hb hab
        rw [SimpleGraph.mem_neighborSet] at ha
        have hadja := (graph_adj_iff v a).mp ha
        apply Subtype.ext
        have hmem : a.1 ∈ ({v.1, b.1} : Finset GaussianInt) := by
          rw [← hab]
          simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact hmem.resolve_left (fun h => hadja.1 (Subtype.ext h.symm))
      · intro e he
        rcases he with ⟨heE, hve⟩
        obtain ⟨a, b, hab, heq⟩ :=
          Finset.card_eq_two.mp (boundary_edge_card_two e heE)
        subst e
        simp only [Finset.mem_insert, Finset.mem_singleton] at hve
        rcases hve with rfl | rfl
        · have hbV : b ∈ BoundaryFootprintVertices T := by
            rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty]
            exact ⟨{v.1, b}, heE, by simp⟩
          let w : BV := ⟨b, hbV⟩
          have hvw : v ≠ w := by
            intro h
            exact hab (congrArg Subtype.val h)
          refine ⟨w, ?_, ?_⟩
          · rw [SimpleGraph.mem_neighborSet]
            exact (graph_adj_iff v w).mpr ⟨hvw, heE⟩
          · rfl
        · have haV : a ∈ BoundaryFootprintVertices T := by
            rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty]
            exact ⟨{a, v.1}, heE, by simp⟩
          let w : BV := ⟨a, haV⟩
          have hvw : v ≠ w := by
            intro h
            exact hab (congrArg Subtype.val h).symm
          refine ⟨w, ?_, ?_⟩
          · rw [SimpleGraph.mem_neighborSet]
            apply (graph_adj_iff v w).mpr
            refine ⟨hvw, ?_⟩
            rw [Finset.pair_comm]
            exact heE
          · simp [w, Finset.pair_comm]
    _ = 2 := boundary_degree_two v.1 v.2

end BoundaryComponentCycle

private theorem boundaryEdgeFourNeighbor (T : ProtoTile) (a b : GaussianInt)
      (hab : ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      FourNeighborAdjacent a b := by
  have boundary_edge_card_two (e : Finset GaussianInt) (he : e ∈ BoundaryFootprintEdges T) :
      e.card = 2 := BoundaryComponentCycle.boundary_edge_card_two T e he
  have habne : a ≠ b := by
    intro h
    subst b
    have hc := boundary_edge_card_two {a, a} hab
    simp at hc
  rcases hab with ⟨q, (⟨heq, _⟩ | ⟨heq, _⟩)⟩
  · have ha : a ∈ ({q, q + 1} : Finset GaussianInt) := by rw [← heq]; simp
    have hb : b ∈ ({q, q + 1} : Finset GaussianInt) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · exact (habne rfl).elim
      · simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · rcases hb with rfl | rfl
      · simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
      · exact (habne rfl).elim
  · have ha : a ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← heq]; simp
    have hb : b ∈ ({q, q + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · exact (habne rfl).elim
      · simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    · rcases hb with rfl | rfl
      · simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
      · exact (habne rfl).elim

theorem P5620T1BoundaryComponentCycle (T : ProtoTile)
    (cells_nonempty : T.cells.Nonempty)
    (boundary_degree_two :
      ∀ v ∈ BoundaryFootprintVertices T,
        Set.ncard {e : Finset GaussianInt |
          e ∈ BoundaryFootprintEdges T ∧ v ∈ e} = 2) :
    ∃ (p : List GaussianInt) (x y z : GaussianInt),
      p.Nodup ∧ 4 ≤ p.length ∧
      p.head? = some x ∧ p.getLast? = some y ∧
      List.IsChain (fun a b =>
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) p ∧
      ({y, x} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∧
      List.IsChain FourNeighborAdjacent p ∧ FourNeighborAdjacent y x ∧
      (∀ a b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b) ∧
      (∀ a ∈ p, a ∈ BoundaryFootprintVertices T) ∧
      z ∈ T.cells ∧ (∀ q ∈ T.cells, q.re ≤ z.re) ∧ z + 1 ∉ T.cells ∧
      let cyclicEdges := (p.zip p.tail) ++ [(y, x)]
      (∀ a b, (a, b) ∈ cyclicEdges →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) ∧
      (∀ a b, (a, b) ∈ cyclicEdges → FourNeighborAdjacent a b) ∧
      (∀ a b, a ∈ p →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T →
        (a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges) ∧
      ((z + 1, z + 1 + ⟨0, 1⟩) ∈ cyclicEdges ∨
        (z + 1 + ⟨0, 1⟩, z + 1) ∈ cyclicEdges) := by
-- BODY
  classical
  have boundary_vertices_finite : (BoundaryFootprintVertices T).Finite :=
      BoundaryFootprintVertices.finite T
  let BV := {v : GaussianInt // v ∈ BoundaryFootprintVertices T}
  let : Fintype BV := boundary_vertices_finite.fintype
  let G : SimpleGraph BV := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have boundary_edge_card_two (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e.card = 2 :=
          BoundaryComponentCycle.boundary_edge_card_two T e he
  have graph_adj_iff (a b : BV) :
      G.Adj a b ↔
        a ≠ b ∧ ({a.1, b.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T :=
            BoundaryComponentCycle.graph_adj_iff T a b
  have graph_isCycles : G.IsCycles := BoundaryComponentCycle.graph_isCycles T cells_nonempty
      boundary_degree_two
  obtain ⟨z, hz, hmax⟩ := T.cells.exists_max_image (fun q => q.re) cells_nonempty
  have hzout : z + 1 ∉ T.cells := by
    intro hz1
    have hle := hmax (z + 1) hz1
    simp at hle
  have hrightEdge : ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges T := by
    refine ⟨z + 1, Or.inr ⟨rfl, Or.inr ⟨hzout, ?_⟩⟩⟩
    simpa [Zsqrtd.ext_iff] using hz
  have hrightVertex : z + 1 ∈ BoundaryFootprintVertices T := by
    rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty]
    exact ⟨{z + 1, z + 1 + ⟨0, 1⟩}, hrightEdge, by simp⟩
  have hrightTopVertex : z + 1 + ⟨0, 1⟩ ∈ BoundaryFootprintVertices T := by
    rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty]
    exact ⟨{z + 1, z + 1 + ⟨0, 1⟩}, hrightEdge, by simp⟩
  let v0 : BV := ⟨z + 1, hrightVertex⟩
  let v1 : BV := ⟨z + 1 + ⟨0, 1⟩, hrightTopVertex⟩
  have hv01 : G.Adj v0 v1 := by
    apply (graph_adj_iff v0 v1).mpr
    refine ⟨?_, hrightEdge⟩
    intro h
    have hi := congrArg (fun q : BV => q.1.im) h
    simp [v0, v1] at hi
  let component := G.connectedComponentMk v0
  have hv0component : v0 ∈ component.supp := rfl
  have hv0neighbor : (G.neighborSet v0).Nonempty :=
    ⟨v1, by rw [SimpleGraph.mem_neighborSet]; exact hv01⟩
  obtain ⟨p, x, y, hpNodup, hpLength, hpHead, hpLast, hpVerts,
      hyx, hpChain, hpEdges⟩ :=
    FiniteCycleComponentList G graph_isCycles component v0 hv0component hv0neighbor
  let gridPath : List GaussianInt := p.map Subtype.val
  have gridPath_nodup : gridPath.Nodup := hpNodup.map Subtype.val_injective
  have gridPath_length : 3 ≤ gridPath.length := by simpa [gridPath] using hpLength
  have gridPath_head : gridPath.head? = some x.1 := by
    simp only [gridPath, List.head?_map, hpHead, Option.map_some]
  have gridPath_last : gridPath.getLast? = some y.1 := by
    simp only [gridPath, List.getLast?_map, hpLast, Option.map_some]
  have gridPath_chain : List.IsChain (fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) gridPath := by
    change List.IsChain (fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) (p.map Subtype.val)
    rw [List.isChain_map]
    exact hpChain.imp fun a b hab => ((graph_adj_iff a b).mp hab).2
  have gridPath_close :
      ({y.1, x.1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T :=
    ((graph_adj_iff y x).mp hyx).2
  have boundary_edge_fourNeighbor (a b : GaussianInt)
      (hab : ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      FourNeighborAdjacent a b :=
    boundaryEdgeFourNeighbor T a b hab
  have gridPath_fourNeighbor : List.IsChain FourNeighborAdjacent gridPath :=
    gridPath_chain.imp fun a b hab => boundary_edge_fourNeighbor a b hab
  have gridPath_close_fourNeighbor : FourNeighborAdjacent y.1 x.1 :=
    boundary_edge_fourNeighbor y.1 x.1 gridPath_close
  have gridPath_zip_fourNeighbor :
      ∀ a b, (a, b) ∈ gridPath.zip gridPath.tail → FourNeighborAdjacent a b := by
    intro a b hab
    rw [List.mem_iff_getElem] at hab
    rcases hab with ⟨i, hi, hab⟩
    have hi' : i < gridPath.tail.length := by
      simpa [List.length_zip] using hi
    have hip : i + 1 < gridPath.length := by
      simp only [List.length_tail] at hi'
      omega
    rw [List.getElem_zip, List.getElem_tail] at hab
    injection hab with ha hb
    rw [List.isChain_iff_getElem] at gridPath_fourNeighbor
    simpa [ha, hb] using gridPath_fourNeighbor i hip
  let cyclicEdges := (gridPath.zip gridPath.tail) ++ [(y.1, x.1)]
  have gridPath_zip_boundary :
      ∀ a b, (a, b) ∈ gridPath.zip gridPath.tail →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    intro a b hab
    rw [List.mem_iff_getElem] at hab
    rcases hab with ⟨i, hi, hab⟩
    have hi' : i < gridPath.tail.length := by
      simpa [List.length_zip] using hi
    have hip : i + 1 < gridPath.length := by
      simp only [List.length_tail] at hi'
      omega
    rw [List.getElem_zip, List.getElem_tail] at hab
    injection hab with ha hb
    rw [List.isChain_iff_getElem] at gridPath_chain
    simpa [ha, hb] using gridPath_chain i hip
  have cyclic_edge_boundary (a b : GaussianInt) (hab : (a, b) ∈ cyclicEdges) :
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    simp only [cyclicEdges, List.mem_append, List.mem_singleton] at hab
    rcases hab with hab | hab
    · exact gridPath_zip_boundary a b hab
    · have hab' : a = y.1 ∧ b = x.1 := Prod.mk.inj hab
      simpa [hab'.1, hab'.2] using gridPath_close
  have component_graph_edge_cyclic (a b : BV) (ha : a ∈ component.supp)
      (hab : G.Adj a b) :
      (a.1, b.1) ∈ cyclicEdges ∨ (b.1, a.1) ∈ cyclicEdges := by
    rcases (hpEdges a b ha).mp hab with hclose | hopen
    · rcases Sym2.eq_iff.mp hclose with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (by simp [cyclicEdges])
      · exact Or.inr (by simp [cyclicEdges])
    · rw [List.mem_iff_getElem] at hopen
      rcases hopen with ⟨i, hi, hopen⟩
      have hi' : i < p.tail.length := by
        simpa [List.length_zipWith] using hi
      have hip : i + 1 < p.length := by
        simp only [List.length_tail] at hi'
        omega
      rw [List.getElem_zipWith, List.getElem_tail] at hopen
      have hpPair : (p[i].1, p[i + 1].1) ∈ gridPath.zip gridPath.tail := by
        rw [List.mem_iff_getElem]
        refine ⟨i, ?_, ?_⟩
        · simpa [gridPath, List.length_zip, List.length_zipWith] using hi
        · rw [List.getElem_zip, List.getElem_tail]
          simp [gridPath]
      rcases Sym2.eq_iff.mp hopen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (by simp [cyclicEdges, hpPair])
      · exact Or.inr (by simp [cyclicEdges, hpPair])
  have hrightCyclic :
      (z + 1, z + 1 + ⟨0, 1⟩) ∈ cyclicEdges ∨
        (z + 1 + ⟨0, 1⟩, z + 1) ∈ cyclicEdges := by
    simpa [v0, v1] using
      component_graph_edge_cyclic v0 v1 hv0component hv01
  have gridPath_length_four : 4 ≤ gridPath.length := by
    by_contra hfour
    have hlen : gridPath.length = 3 := by omega
    rcases List.length_eq_three.mp hlen with ⟨a, b, c, hpath⟩
    have hab : FourNeighborAdjacent a b := by
      rw [hpath] at gridPath_fourNeighbor
      simpa using gridPath_fourNeighbor.rel
    have hbc : FourNeighborAdjacent b c := by
      rw [hpath] at gridPath_fourNeighbor
      simpa using gridPath_fourNeighbor.tail.rel
    have hxa : x.1 = a := by
      rw [hpath] at gridPath_head
      exact (Option.some.inj gridPath_head).symm
    have hyc : y.1 = c := by
      rw [hpath] at gridPath_last
      exact (Option.some.inj gridPath_last).symm
    have hca : FourNeighborAdjacent c a := by
      simpa [hxa, hyc] using gridPath_close_fourNeighbor
    have step_sum (u v : GaussianInt) (huv : FourNeighborAdjacent u v) :
        (v.re : Int) + v.im = (u.re : Int) + u.im + 1 ∨
          (v.re : Int) + v.im = (u.re : Int) + u.im - 1 := by
      rcases huv with rfl | rfl | rfl | rfl <;>
        simp [] <;> omega
    rcases step_sum a b hab with habs | habs <;>
      rcases step_sum b c hbc with hbcs | hbcs <;>
      rcases step_sum c a hca with hcas | hcas <;> omega
  have gridPath_mem_boundary (a : GaussianInt) (ha : a ∈ gridPath) :
      a ∈ BoundaryFootprintVertices T := by
    rcases List.mem_map.mp ha with ⟨v, _, rfl⟩
    exact v.property
  have component_edge_cyclic (a b : GaussianInt) (ha : a ∈ gridPath)
      (hab : ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      (a, b) ∈ cyclicEdges ∨ (b, a) ∈ cyclicEdges := by
    rcases List.mem_map.mp ha with ⟨v, hv, rfl⟩
    have hb : b ∈ BoundaryFootprintVertices T := by
      rw [BoundaryFootprintVertices, ite_eq_left cells_nonempty]
      exact ⟨{v.1, b}, hab, by simp⟩
    let w : BV := ⟨b, hb⟩
    have hvw : v ≠ w := by
      intro heq
      have hval : v.1 = b := congrArg Subtype.val heq
      have hc := boundary_edge_card_two {v.1, b} hab
      simp [hval] at hc
    apply component_graph_edge_cyclic v w ?_
      ((graph_adj_iff v w).mpr ⟨hvw, hab⟩)
    rw [← hpVerts, Finset.mem_coe, List.mem_toFinset]
    exact hv
  refine ⟨gridPath, x.1, y.1, z, gridPath_nodup, gridPath_length_four,
    gridPath_head, gridPath_last, gridPath_chain, gridPath_close,
    gridPath_fourNeighbor, gridPath_close_fourNeighbor, gridPath_zip_fourNeighbor,
    gridPath_mem_boundary, hz, hmax, hzout, cyclic_edge_boundary, ?_,
    component_edge_cyclic, hrightCyclic⟩
  intro a b hab
  exact boundary_edge_fourNeighbor a b (cyclic_edge_boundary a b hab)

end ApollonianSuperharmonic

end
