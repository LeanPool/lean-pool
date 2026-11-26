/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM10.Section8

/-!
# The tangle after vertex deletion in Graph Minors XII, (7.3)

Deleting vertices from a drawing agrees with deleting them from its hypergraph.
Thus Graph Minors X, (8.5) supplies the tangle used at the start of the proof of
XII, (7.3), page 261. This file proves that part of the construction. Respectfulness
and the two metric bounds are separate questions.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Vertex deletion in a drawing and in its hypergraph have the same vertices,
edges, and incidence relation. This identifies the two deletions used at the
start of Graph Minors XII, (7.3), page 261. -/
theorem deleteVertices_toHypergraph (Γ : Drawing S) (Z : Set S) :
    (deleteVertices Γ Z).toHypergraph = Γ.toHypergraph.deleteVertices Z := by
  have hsub := deleteVertices_isSubdrawing Γ Z
  have heq : (deleteVertices Γ Z).E =
      {e ∈ Γ.E | ∀ v ∈ Z, ¬ Γ.toHypergraph.Inc e v} := by
    rw [deleteVertices_E]
    ext e
    constructor
    · rintro ⟨he, hd⟩
      exact ⟨he, fun v hv hi => disjoint_left.mp hd ⟨hi.2.2, hi.2.1⟩ hv⟩
    · rintro ⟨he, hn⟩
      exact ⟨he, disjoint_left.mpr fun v hv hz => hn v hz ⟨he, hv.2, hv.1⟩⟩
  apply Hypergraph.ext
  · exact deleteVertices_V Γ Z
  · exact heq
  · funext e v
    apply propext
    constructor
    · rintro ⟨he, hv, hc⟩
      refine ⟨⟨hsub.2 he, hsub.1 hv, hc⟩, ?_⟩
      exact (heq ▸ he).2
    · rintro ⟨hi, hn⟩
      refine ⟨heq.symm ▸ ⟨hi.1, hn⟩, ?_, hi.2.2⟩
      rw [deleteVertices_V]
      exact ⟨hi.2.1, fun hv => hn v hv hi⟩

omit [T2Space S] in
/-- Every edge of the hypergraph of a drawing has one or two ends, as required
when applying Graph Minors X, (8.5) in XII, (7.3). -/
theorem drawing_toHypergraph_isGraph (Γ : Drawing S) : Γ.toHypergraph.IsGraph := by
  intro e he
  have hends : Γ.toHypergraph.ends e = closure e ∩ Γ.V := by
    ext v
    exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨he, h.2, h.1⟩⟩
  rw [hends]
  rcases Γ.edge_cond e he with ⟨x, y, _, hxy, _⟩ | ⟨x, hx, _⟩
  · rw [hxy]
    refine ⟨⟨x, mem_insert x _⟩, ?_⟩
    simpa only [ncard_singleton] using ncard_insert_le x ({y} : Set S)
  · rw [hx, ncard_singleton]
    exact ⟨singleton_nonempty x, by omega⟩

/-- The tangle part of the construction in Graph Minors XII, (7.3), page 261.
For a set of fewer than `θ` vertices, this is exactly X, (8.5), after identifying
the hypergraph of the deleted drawing. -/
theorem deleteVertices_isTangle {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {Z : Set S}
    (hZ : Z ⊆ Γ.V) (hcard : Z.ncard < θ) :
    IsTangle (deleteVertices Γ Z).toHypergraph (θ - Z.ncard)
      (deleteVerticesTangle Γ.toHypergraph Z T θ) := by
  rw [deleteVertices_toHypergraph]
  exact GM10.theorem_8_5_proof (drawing_toHypergraph_isGraph Γ) hT hZ hcard

/-- At a single vertex, the tangle constructed at the start of XII, (7.3)
has order `θ - 1`. No assumption about two-cellness is needed for this part. -/
theorem theorem_7_3_tangle {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} (hv : v ∈ Γ.V) :
    IsTangle (deleteVertices Γ {v}).toHypergraph (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) := by
  have hcard : ({v} : Set S).ncard < θ := by rw [ncard_singleton]; omega
  simpa only [ncard_singleton] using
    deleteVertices_isTangle hT (singleton_subset_iff.mpr hv) hcard

end GraphMinor.GM12
