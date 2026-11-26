/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM16.ConnectedBoundary
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Two boundary circuits joined by a path

Each circuit is connected. A path between the two circuits therefore
connects all boundary vertices inside the annular subgraph. The
connected-boundary lemma then connects every other vertex. This is
the combinatorial part of XVI (8.1), Claim (14).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06
universe u v

/-- The graph of a circuit drawing is connected, since prefixes of
its defining closed walk join every vertex to the initial vertex. -/
theorem circuit_drawing_isGraphConnected {S : Type u} [TopologicalSpace S]
    {C : Drawing S} (hC : C.IsCircuit) : IsGraphConnected C.toGraph := by
  change C.V.Nonempty ∧ ∀ x ∈ C.V, ∀ y ∈ C.V, Nonempty (GraphWalk C.toGraph x y)
  obtain ⟨a, W, _, _, hV, _⟩ := hC
  refine ⟨⟨a, hV.symm ▸ W.start_mem_support⟩, ?_⟩
  intro x hx y hy
  rw [hV] at hx hy
  obtain ⟨W₁, _, _⟩ := W.exists_append_of_mem hx
  obtain ⟨W₂, _, _⟩ := W.exists_append_of_mem hy
  exact ⟨W₁.reverse.append W₂⟩

/-- Two connected boundary subgraphs joined inside a subgraph form
a connected boundary. Retaining all edges away from this boundary
then makes the entire subgraph connected. -/
theorem isGraphConnected_of_two_boundaries {α : Type u} {β : Type v}
    {G Q I O : Graph α β} {a b : α}
    (hQG : Q ≤ G) (hG : IsGraphConnected G)
    (hIQ : I ≤ Q) (hOQ : O ≤ Q) (hI : IsGraphConnected I) (hO : IsGraphConnected O)
    (ha : a ∈ V(I)) (hb : b ∈ V(O)) (W : GraphWalk Q a b)
    (hKeep : ∀ e x y, G.IsLink e x y → x ∈ V(Q) →
      x ∉ V(I) ∪ V(O) → Q.IsLink e x y) : IsGraphConnected Q := by
  have hToA : ∀ x ∈ V(I) ∪ V(O), Nonempty (GraphWalk Q x a) := by
    intro x hx
    rcases hx with hxI | hxO
    · obtain ⟨R⟩ := hI.2 x hxI a ha
      obtain ⟨R', _, _⟩ := GraphMinor.GM09.exists_walk_up_of_le hIQ R
      exact ⟨R'⟩
    · obtain ⟨R⟩ := hO.2 x hxO b hb
      obtain ⟨R', _, _⟩ := GraphMinor.GM09.exists_walk_up_of_le hOQ R
      exact ⟨R'.append W.reverse⟩
  apply isGraphConnected_of_connected_boundary hQG hG ⟨a, Or.inl ha⟩
    (union_subset hIQ.vertexSet_mono hOQ.vertexSet_mono) _ hKeep
  intro x hx y hy
  obtain ⟨R⟩ := hToA x hx
  obtain ⟨T⟩ := hToA y hy
  exact ⟨R.append T.reverse⟩

end GraphMinor.GM16
