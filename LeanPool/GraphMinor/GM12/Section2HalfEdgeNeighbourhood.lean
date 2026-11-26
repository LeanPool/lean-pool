/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation

/-!
# A drawing near a vertex consists of its short half-edges

For the entry-edge construction of XII page 243, it is useful to remove
all but prescribed positive initial pieces of the incident edges.
The remaining parts are compact and miss the vertex. Their complement
is the required neighbourhood. The proof also applies to isolated
vertices and loops.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- Prescribed positive initial pieces of every half-edge cover the
drawing in a neighbourhood of the vertex, together with the vertex
itself. Compact edge remainders can all be excluded at once. -/
theorem exists_halfEdge_neighbourhood {S : Type*} [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    (τ : halfEdges Γ γ v → I) (hτ0 : ∀ i, 0 < τ i) :
    ∃ O : Set S, IsOpen O ∧ v ∈ O ∧
      O ∩ Γ.U ⊆ {v} ∪ ⋃ i : halfEdges Γ γ v, spoke γ i.val '' Icc 0 (τ i) := by
  obtain ⟨K, hKclosed, hvK, hUsub⟩ := exists_closed_drawingAwayFromSpokes hγ hv τ hτ0
  refine ⟨Kᶜ, hKclosed.isOpen_compl, hvK, ?_⟩
  intro x hx
  exact (hUsub hx.2).resolve_left hx.1

end GraphMinor.GM12
