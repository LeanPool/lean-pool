/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Section88

/-!
# Composition along the inner circle of an annulus

Split the drawing in the outer disc into its inner-disc part and
its annular part. Assign the edges on the inner circle to the
annular part. The two parts then form a separation, whose common
vertices are exactly the inner boundary vertices. This is the
society composition required in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM06 GraphMinor.GM11
  GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- A drawn annulus composes with the graph inside its inner circle.
All common boundary edges are assigned to the annular graph. -/
theorem exists_annular_composition (H : Drawing S) {D E : Set S}
    (hD : IsClosed D) (hE : IsClosed E) (hED : E ⊆ D)
    (hCircle : IsOArc (frontier E)) (hBd : frontier E ⊆ H.U)
    (N : Neighborhood S (Set S))
    (hNG : N.G = (H.interSet (D \ interior E)).toGraph)
    (hInner : N.Ω₀.bar = (H.interSet (D \ interior E)).V ∩ frontier E) :
    ∃ S_comp S₀ : Society S (Set S),
      S_comp.G = (H.interSet D).toGraph ∧ S_comp.Ω = N.Ω ∧
      S₀.G = (H.interSet E).toGraph.deleteEdges E(N.G) ∧
      S_comp.IsComposition S₀ N := by
  classical
  let A := D \ interior E
  have hA : IsClosed A := hD.sdiff isOpen_interior
  let J := H.interSet D
  let Q := H.interSet A
  let K := H.interSet E
  have hQH : Q.IsSubdrawing H := interSet_isSub
  have hKH : K.IsSubdrawing H := interSet_isSub
  have hQJ : Q.IsSubdrawing J := subdrawing_interSet_of_U_subset hQH
    ((interSet_U_subset hA).trans sdiff_subset)
  have hKJ : K.IsSubdrawing J := subdrawing_interSet_of_U_subset hKH
    ((interSet_U_subset hE).trans hED)
  have hQle : Q.toGraph ≤ J.toGraph := toGraph_le_of_isSubdrawing hQJ
  have hKle : K.toGraph ≤ J.toGraph := toGraph_le_of_isSubdrawing hKJ
  have hNG' : N.G = Q.toGraph := hNG
  let R := K.toGraph.deleteEdges E(N.G)
  have hRle : R ≤ J.toGraph := deleteEdges_le.trans hKle
  have hV : V(R) ∪ V(N.G) = V(J.toGraph) := by
    rw [hNG']
    change K.V ∪ Q.V = J.V
    ext x
    simp only [K, Q, J, mem_union, mem_interSet_V_iff hE, mem_interSet_V_iff hA,
      mem_interSet_V_iff hD]
    change (x ∈ H.V ∧ x ∈ E) ∨ (x ∈ H.V ∧ x ∈ D ∧ x ∉ interior E) ↔
      x ∈ H.V ∧ x ∈ D
    constructor
    · rintro (⟨hx, hxe⟩ | ⟨hx, hxd, _⟩)
      · exact ⟨hx, hED hxe⟩
      · exact ⟨hx, hxd⟩
    · rintro ⟨hx, hxd⟩
      by_cases hxe : x ∈ E
      · exact Or.inl ⟨hx, hxe⟩
      · exact Or.inr ⟨hx, hxd, fun hxi => hxe (interior_subset hxi)⟩
  have hEdgeCover : K.E ∪ Q.E = J.E := by
    ext e
    simp only [K, Q, J, mem_union, mem_interSet_E_iff]
    constructor
    · rintro (⟨he, heE⟩ | ⟨he, heA⟩)
      · exact ⟨he, heE.trans hED⟩
      · exact ⟨he, heA.trans sdiff_subset⟩
    · rintro ⟨he, heD⟩
      rcases edge_subset_or_disjoint_of_isOArc hCircle hBd he with heb | hed
      · exact Or.inl ⟨he, heb.trans hE.frontier_subset⟩
      · rcases GM14.subset_or_disjoint_of_frontier hE he.2.2.1.isConnected.isPreconnected hed with
          hs | hd
        · exact Or.inl ⟨he, hs⟩
        · exact Or.inr ⟨he, fun x hx => ⟨heD hx, fun hxi =>
            hd.notMem_of_mem_left hx (interior_subset hxi)⟩⟩
  have hEdges : E(R) ∪ E(N.G) = E(J.toGraph) := by
    change (K.E \ E(N.G)) ∪ E(N.G) = J.E
    rw [hNG']
    change (K.E \ Q.E) ∪ Q.E = J.E
    rw [← hEdgeCover]
    ext e
    simp only [mem_union, mem_sdiff]
    tauto
  have hInter : V(R) ∩ V(N.G) = N.Ω₀.bar := by
    rw [hInner, hNG']
    change K.V ∩ Q.V = Q.V ∩ frontier E
    ext x
    simp only [K, mem_inter_iff, mem_interSet_V_iff hE]
    constructor
    · rintro ⟨⟨hxH, hxE⟩, hxQ⟩
      have hxOut : x ∉ interior E := ((mem_interSet_V_iff hA).mp hxQ).2.2
      exact ⟨hxQ, subset_closure hxE, hxOut⟩
    · rintro ⟨hxQ, hxf⟩
      exact ⟨⟨((mem_interSet_V_iff hA).mp hxQ).1, hE.frontier_subset hxf⟩, hxQ⟩
  let S_comp : Society S (Set S) :=
    ⟨J.toGraph, N.Ω, J.finite_V, J.finite_edges,
      fun x hx => hQle.vertexSet_mono (hNG' ▸ N.bar_subset hx)⟩
  let S₀ : Society S (Set S) :=
    ⟨R, N.Ω₀, K.finite_V, K.finite_edges.subset sdiff_subset,
      fun x hx => (hInter.symm ▸ hx).1⟩
  refine ⟨S_comp, S₀, rfl, rfl, rfl, ?_, rfl, rfl, hInter.symm⟩
  refine ⟨⟨hRle, hNG'.symm ▸ hQle, hV, hEdges, ?_⟩, N.bar_subset⟩
  change Disjoint (K.E \ E(N.G)) E(N.G)
  exact disjoint_sdiff_left

end GraphMinor.GM16
