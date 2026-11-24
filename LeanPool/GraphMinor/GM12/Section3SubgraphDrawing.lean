/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Reading an abstract subgraph as a subdrawing

VI (3.6), applied in XII (3.2), page 247, gives an abstract forest
subgraph. Retain its vertices and edges in the drawing. Every end
of a retained edge is already a retained vertex, so this span adds
no vertices. Its graph links are exactly those of the abstract
subgraph. This permits the return from VI's objects to XII's
connected subdrawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 Graph

/-- Every abstract subgraph of a drawing is the graph of a subdrawing,
with the same vertices and edges. -/
theorem exists_subdrawing_of_subgraph
    {S : Type*} [TopologicalSpace S] [T1Space S] (Γ : Drawing S)
    (H : Graph S (Set S)) (hH : H ≤ Γ.toGraph) :
    ∃ D : Drawing S, D.IsSubdrawing Γ ∧ D.V = H.vertexSet ∧ D.toGraph = H := by
  let D := Γ.span H.vertexSet H.edgeSet
  have hDV : D.V = H.vertexSet := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨e, ⟨heH, _⟩, hxcl, hxV⟩ := mem_iUnion₂.mp hx
        obtain ⟨u, v, hl⟩ := (H.edge_mem_iff_exists_isLink e).mp heH
        have hlG := hH.isLink_mono hl
        have hxends : x ∈ ({u, v} : Set S) := hlG.2.2.2 ▸ ⟨hxcl, hxV⟩
        rcases hxends with rfl | rfl
        · exact hl.left_mem
        · exact hl.right_mem
    · intro x hx
      exact Or.inl ⟨hx, hH.vertexSet_mono hx⟩
  have hDE : D.E = H.edgeSet := (Γ.span_E _ _).trans (inter_eq_left.mpr hH.edgeSet_mono)
  have hsub : D.IsSubdrawing Γ := Γ.span_isSubdrawing _ _
  refine ⟨D, hsub, hDV, ?_⟩
  apply Graph.ext hDV
  intro e x y
  constructor
  · intro hl
    have heH : e ∈ H.edgeSet := hDE ▸ hl.1
    exact (hH.isLink_iff heH).mpr ((hsub.isLink_iff hl.1).mp hl)
  · intro hl
    have heD : e ∈ D.E := hDE.symm ▸ hl.edge_mem
    exact (hsub.isLink_iff heD).mpr (hH.isLink_mono hl)

end GraphMinor.GM12
