/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import Mathlib.Data.Set.Card.Arithmetic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Counting graph contacts over closed edges

The count on page 226 of VII (4.6) sums the vertex contacts on closed
edges of `L`. Every vertex of `L` is on an edge. Thus the closed edges
cover its point set, and summing their contact bounds gives the required
bound without dropping vertex contacts.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The closed edges cover a drawing with no isolated vertices. -/
theorem U_eq_closed_edges_of_no_isolated {S : Type*} [TopologicalSpace S]
    (L : Drawing S) (hno : HasNoIsolatedVertices L) :
    L.U = ⋃ e ∈ L.E, closure e := by
  apply Subset.antisymm
  · intro x hx
    rw [L.U_eq] at hx
    rcases hx with hx | hx
    · obtain ⟨e, he, hi⟩ := hno x hx
      exact mem_iUnion₂.mpr ⟨e, he, hi.2.2⟩
    · exact hx
  · intro x hx
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact L.closure_subset_U he hxe

/-- The closed-edge contact sum used for `L` in VII (4.6), page 226. -/
theorem ncard_vertex_contacts_U_le_edges_mul {S : Type*} [TopologicalSpace S]
    (G L : Drawing S) (hno : HasNoIsolatedVertices L) {B : ℕ}
    (hbound : ∀ e ∈ L.E, (closure e ∩ G.V).ncard ≤ B) :
    (G.V ∩ L.U).ncard ≤ L.E.ncard * B := by
  classical
  have hcover : G.V ∩ L.U = ⋃ e ∈ L.finite_edges.toFinset, closure e ∩ G.V := by
    ext x
    constructor
    · rintro ⟨hxV, hxU⟩
      have hx := (congrArg (fun A => x ∈ A) (U_eq_closed_edges_of_no_isolated L hno)).mp hxU
      obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨e, L.finite_edges.mem_toFinset.mpr he, hxe, hxV⟩
    · intro hx
      obtain ⟨e, he, hxe, hxV⟩ := mem_iUnion₂.mp hx
      exact ⟨hxV, L.closure_subset_U (L.finite_edges.mem_toFinset.mp he) hxe⟩
  rw [hcover, ncard_eq_toFinset_card L.E L.finite_edges]
  calc
    _ ≤ ∑ e ∈ L.finite_edges.toFinset, (closure e ∩ G.V).ncard :=
      L.finite_edges.toFinset.set_ncard_biUnion_le _
    _ ≤ ∑ _e ∈ L.finite_edges.toFinset, B :=
      Finset.sum_le_sum fun e he => hbound e (L.finite_edges.mem_toFinset.mp he)
    _ = L.finite_edges.toFinset.card * B := by simp

end GraphMinor.GM07
