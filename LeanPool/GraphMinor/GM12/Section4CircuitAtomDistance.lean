/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1b
import LeanPool.GraphMinor.GM12.Section4CircuitWalk
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM11.Section4

/-!
# Atoms meeting a short circuit inside are close

Claim (1) in XII (4.3), page 250, puts a nonfree edge and one of
the chosen distant edges in the inside of a radial circuit of length
two. Traverse that circuit once. The corresponding atoms lie in
the walk inside by XII's corresponding-atom lemma, so the traversal
witnesses their distance. Its half-length is the number of original
vertices on the radial circuit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

/-- Atoms meeting the inside of a short radial circuit have distance
at most half the circuit length. This is the metric step of claim
(1) in XII (4.3), page 250. -/
theorem atom_distance_le_circuit_vertex_count
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing K) (hCl : C.length < 2 * θ)
    {x y : Set S} (hx : x ∈ Γ.A) (hy : y ∈ Γ.A)
    (hxC : (x ∩ ins C).Nonempty) (hyC : (y ∩ ins C).Nonempty) :
    tangleMetric Γ K ins θ x y ≤ (C.V ∩ Γ.V).ncard := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x', hx', _⟩ := existsUnique_correspondingAtom hK hx
  obtain ⟨y', hy', _⟩ := existsUnique_correspondingAtom hK hy
  have hCcopy := hC
  obtain ⟨u, U, _, _, hV, _⟩ := hCcopy
  have huC : u ∈ C.V := hV ▸ U.start_mem_support
  obtain ⟨W, hWC, hlen⟩ := circuit_walk_at hC hCs huC
  have hshort : W.length < 2 * θ := hlen ▸ hCl
  have hins : ins C ⊆ insWalk ins K W := by
    intro z hz
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, by rw [hWC]; exact ⟨subset_rfl, subset_rfl⟩⟩, hz⟩)
  have hxW := (corresponding_atom_subset_iff hS hK hd hx' W hshort).mpr
    (hxC.mono (inter_subset_inter_right x hins))
  have hyW := (corresponding_atom_subset_iff hS hK hd hy' W hshort).mpr
    (hyC.mono (inter_subset_inter_right y hins))
  exact tangleMetric_le_of_walk hx' hy' W hshort
    (hlen.trans (circuit_length_eq_two_mul_ncard hK.2.1 hC hCs).1) hxW hyW

end GraphMinor.GM12
