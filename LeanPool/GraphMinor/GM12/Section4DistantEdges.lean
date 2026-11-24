/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4EdgeCircuit
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges
import LeanPool.GraphMinor.GM12.Section1b
import LeanPool.GraphMinor.GM11.CitedResults

/-!
# The two distant edges at the start of XII (4.3)

A tangle of order at least three requires at least two drawing
edges. Otherwise the small side consisting of its only edge would
cover every edge, contrary to X (2.3). Thus the corrected edge-count
hypothesis of XII (1.2) holds in the application on page 249.
Applying (1.2) to any edge supplies the two distant edges.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM11 GM14 Hypergraph

/-- The edge-count condition needed to apply XII (1.2) in (4.3). -/
theorem two_le_edge_count_of_tangle_order_three
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) (hθ : 2 < θ) : 2 ≤ Γ.E.ncard := by
  obtain ⟨e, he⟩ := edges_nonempty_of_tangle_order_two hT (by omega)
  have hm := edge_small_side_mem_of_order_three hT hθ he
  have hnot := GM10.theorem_2_3_proof hT (by omega) hm hm hm
  by_contra hcard
  have hcard' : Γ.E.ncard ≤ 1 := by omega
  have hsingle : Γ.E = {e} := by
    apply Set.Subset.antisymm
    · intro f hf
      exact Set.mem_singleton_iff.mpr ((Set.ncard_le_one Γ.finite_edges).mp hcard' f hf e he)
    · exact Set.singleton_subset_iff.mpr he
  apply hnot
  simp only [GM10.union_self]
  change ({e} : Set (Set S)) = Γ.E
  exact hsingle.symm

/-- The two edges chosen at the start of XII (4.3), page 249. -/
theorem exists_two_edges_at_tangle_order_distance
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d) (hθ : 2 < θ) :
    ∃ g ∈ Γ.E, ∃ h ∈ Γ.E, d g h = θ := by
  have hcount := two_le_edge_count_of_tangle_order_three hm.1.2.1 hθ
  obtain ⟨g, hg⟩ := (Set.ncard_pos Γ.finite_edges).mp (show 0 < Γ.E.ncard by omega)
  obtain ⟨h, hh, hdist⟩ := theorem_1_2_proof hS hm
    hcount (Or.inl (Or.inr hg))
  exact ⟨g, hg, h, hh, hdist⟩

end GraphMinor.GM12
