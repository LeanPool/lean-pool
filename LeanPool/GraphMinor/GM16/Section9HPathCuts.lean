/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Menger
import LeanPool.GraphMinor.GM09.Basic
import Mathlib.Combinatorics.Graph.Delete

/-!
# Separators for paths between battlefield boundaries

In XVI (8.1), Claim (5), Menger is applied after removing the edges
of the cleared drawing and its vertices outside the two boundary sets.
Trimming a path between the two sets then gives a path whose only
vertices in the drawing are its ends.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- The graph used for the pair of boundary sets in the Menger argument
of XVI (8.1), Claim (5), page 72. -/
def boundaryPathGraph {α : Type u} {β : Type v} (G H : Graph α β) (X Y : Set α) : Graph α β :=
  (G.deleteVerts (V(H) \ (X ∪ Y))).deleteEdges E(H)

/-- The auxiliary graph is a subgraph of the ambient graph. -/
theorem boundaryPathGraph_le {α : Type u} {β : Type v}
    (G H : Graph α β) (X Y : Set α) : boundaryPathGraph G H X Y ≤ G :=
  deleteEdges_le.trans deleteVerts_le

/-- Vertices of the drawing retained in the auxiliary graph belong to
one of the two boundary sets. -/
theorem boundaryPathGraph_vertex_mem {α : Type u} {β : Type v}
    {G H : Graph α β} {X Y : Set α} {x : α}
    (hx : x ∈ V(boundaryPathGraph G H X Y)) (hxH : x ∈ V(H)) : x ∈ X ∪ Y := by
  change x ∈ V(G.deleteVerts (V(H) \ (X ∪ Y))) at hx
  rw [vertexSet_deleteVerts] at hx
  exact by_contra fun hnot => hx.2 ⟨hxH, hnot⟩

/-- A path trimmed between the two boundary sets is an `H`-path in
`G` when viewed in the auxiliary graph. -/
theorem boundary_fromTo_isHPath {α : Type u} {β : Type v}
    {G H P : Graph α β} {X Y : Set α} {a b : α}
    (hHG : H ≤ G) (hX : X ⊆ V(H)) (hY : Y ⊆ V(H)) (hXY : Disjoint X Y)
    (ha : a ∈ X) (hb : b ∈ Y)
    (hP : IsFromToPathWithEnds (boundaryPathGraph G H X Y) P X Y a b) :
    IsHPathWithEnds G H P a b := by
  have hPG := hP.1.mono (boundaryPathGraph_le G H X Y)
  refine ⟨hHG, hPG, fun heq => hXY.notMem_of_mem_left ha (heq.symm ▸ hb), hX ha, hY hb, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxP, hxH⟩
      rcases boundaryPathGraph_vertex_mem (hP.1.1.vertexSet_mono hxP) hxH with hxX | hxY
      · exact Or.inl (mem_singleton_iff.mp (hP.2.1 ▸ ⟨hxP, hxX⟩))
      · exact Or.inr (mem_singleton_iff.mp (hP.2.2 ▸ ⟨hxP, hxY⟩))
    · rintro (rfl | rfl)
      · exact ⟨hPG.left_mem, hX ha⟩
      · exact ⟨hPG.right_mem, hY hb⟩
  · apply disjoint_left.mpr
    intro e heP heH
    have heK := hP.1.1.edgeSet_mono heP
    change e ∈ E(G.deleteVerts (V(H) \ (X ∪ Y))) \ E(H) at heK
    exact heK.2 heH

/-- Every `H`-path between the two boundary sets lies in the auxiliary
graph used for Menger. -/
theorem hPath_le_boundaryPathGraph {α : Type u} {β : Type v}
    {G H P : Graph α β} {X Y : Set α} {a b : α}
    (ha : a ∈ X) (hb : b ∈ Y) (hP : IsHPathWithEnds G H P a b) :
    P ≤ boundaryPathGraph G H X Y := by
  have hOut : ∀ x ∈ V(P), x ∉ V(H) \ (X ∪ Y) := by
    intro x hxP hx
    have hxEnd : x ∈ ({a, b} : Set α) := hP.2.2.2.2.2.1 ▸ ⟨hxP, hx.1⟩
    rcases hxEnd with rfl | rfl
    · exact hx.2 (Or.inl ha)
    · exact hx.2 (Or.inr hb)
  constructor
  · intro x hx
    change x ∈ V(G.deleteVerts (V(H) \ (X ∪ Y)))
    rw [vertexSet_deleteVerts]
    exact ⟨hP.2.1.1.vertexSet_mono hx, hOut x hx⟩
  · intro e x y hlink
    simp only [boundaryPathGraph, deleteEdges_isLink, deleteVerts_isLink]
    exact ⟨⟨hP.2.1.1.isLink_mono hlink, hOut x hlink.left_mem, hOut y hlink.right_mem⟩,
      fun heH => hP.2.2.2.2.2.2.notMem_of_mem_left hlink.edge_mem heH⟩

/-- The per-pair Menger alternative in XVI (8.1), Claim (5), page 72.
The cut meets the drawing only in the prescribed boundary sets. -/
theorem disjoint_hPaths_or_boundary_separator {α : Type u} {β : Type v}
    (G H : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) (hHG : H ≤ G)
    (X Y : Set α) (hX : X ⊆ V(H)) (hY : Y ⊆ V(H)) (hXY : Disjoint X Y) (k : ℕ) :
    (∃ P : Fin k → Graph α β,
      (∀ i, ∃ a ∈ X, ∃ b ∈ Y, IsHPathWithEnds G H (P i) a b) ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j))) ∨
    (∃ Z ⊆ V(G), Z.ncard < k ∧ Z ∩ V(H) ⊆ X ∪ Y ∧
      ∀ P a b, IsHPathWithEnds G H P a b → a ∈ X → b ∈ Y → (V(P) ∩ Z).Nonempty) := by
  classical
  let K := boundaryPathGraph G H X Y
  have hKG := boundaryPathGraph_le G H X Y
  have hXK : X ⊆ V(K) := by
    intro x hx
    change x ∈ V(G.deleteVerts (V(H) \ (X ∪ Y)))
    rw [vertexSet_deleteVerts]
    exact ⟨hHG.vertexSet_mono (hX hx), fun h => h.2 (Or.inl hx)⟩
  have hYK : Y ⊆ V(K) := by
    intro y hy
    change y ∈ V(G.deleteVerts (V(H) \ (X ∪ Y)))
    rw [vertexSet_deleteVerts]
    exact ⟨hHG.vertexSet_mono (hY hy), fun h => h.2 (Or.inr hy)⟩
  rcases disjoint_fromToPaths_or_separator K (hV.subset hKG.vertexSet_mono)
    (hE.subset hKG.edgeSet_mono) X Y hXK hYK k with ⟨P, hP, hDis⟩ | ⟨Z, hZK, hZcard, hCut⟩
  · refine Or.inl ⟨P, fun i => ?_, hDis⟩
    obtain ⟨a, b, hp⟩ := hP i
    have ha : a ∈ X := ((show a ∈ V(P i) ∩ X from hp.2.1.symm ▸ mem_singleton a)).2
    have hb : b ∈ Y := ((show b ∈ V(P i) ∩ Y from hp.2.2.symm ▸ mem_singleton b)).2
    exact ⟨a, ha, b, hb, boundary_fromTo_isHPath hHG hX hY hXY ha hb hp⟩
  · refine Or.inr ⟨Z, hZK.trans hKG.vertexSet_mono, hZcard, ?_, ?_⟩
    · rintro x ⟨hxZ, hxH⟩
      exact boundaryPathGraph_vertex_mem (hZK hxZ) hxH
    · intro P a b hp ha hb
      exact hCut P a b ⟨hPath_le_boundaryPathGraph ha hb hp, hp.2.1.2⟩ ha hb

end GraphMinor.GM16
