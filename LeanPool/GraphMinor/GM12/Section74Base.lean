/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73
public import LeanPool.GraphMinor.GM12.Section74DeletedRegion
import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# The two-cell-deletion case of XII (7.4)

In the base case of the induction on edges in XII (7.4), pages
262--263, vertex deletion is two-cell. Apply (7.3) for the tangle
and the two lower bounds. The deleted-region lemmas supply the
point-set containment and upper bound two. The whole deleted
drawing is its own component because a two-cell drawing in a
connected closed surface is connected.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14

/-- The base case of XII (7.4), pages 262--263, after establishing
that deletion of the vertex is two-cell. A component is expressed
by its point set being a connected component of the deleted
point set, together with the subdrawing relation. -/
theorem theorem_7_4_of_twoCell_delete
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (Γ' : Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r : Set S),
      Γ'.IsSubdrawing (deleteVertices Γ {v}) ∧
      Γ'.U ∈ componentsIn (deleteVertices Γ {v}).U ∧
      HasTangleMetric Γ' (θ - 1) T' d' ∧ r ∈ Γ'.R ∧ v ∈ r ∧
      Γ.U ⊆ Γ'.U ∪ r ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, ∀ b ∈ Γ.A ∩ Γ'.A, d a b - 2 ≤ d' a b) ∧
      (∀ a ∈ Γ.A ∩ Γ'.A, d a {v} - 1 ≤ d' a r) ∧
      (∀ a ∈ Γ.A, a ⊆ r → d a {v} ≤ 2) := by
  obtain ⟨T', d', r, hm, hr, hvr, hi, hii⟩ := theorem_7_3_proof hS hθ hd hv htwo
  let N := deleteVertices Γ {v}
  have hNpos : 0 < N.V.ncard := by
    have hle := hm.1.2.1.order_le_ncard_vertexSet
    change θ - 1 ≤ N.V.ncard at hle
    omega
  obtain ⟨p, hp⟩ := (ncard_pos N.finite_V).mp hNpos
  have hpU : p ∈ N.U := N.V_subset_U hp
  have hpre : IsPreconnected N.U := isPreconnected_U_of_isTwoCell hS htwo
  have hcomponent : N.U ∈ componentsIn N.U := by
    refine ⟨p, hpU, Subset.antisymm (connectedComponentIn_subset _ _) ?_⟩
    exact hpre.subset_connectedComponentIn hpU Subset.rfl
  exact ⟨N, T', d', r, Drawing.IsSubdrawing.refl N, hcomponent, hm, hr, hvr,
    drawing_subset_delete_union_vertex_region hv hr hvr, hi, hii,
    fun a ha har => atom_in_deleted_vertex_region_distance_le_two hS hθ hd hv hr hvr ha har⟩

end GraphMinor.GM12
