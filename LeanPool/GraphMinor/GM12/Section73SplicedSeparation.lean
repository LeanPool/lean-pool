/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CommonCircuitInside
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# The order bound for the spliced circuit separation

In XII (7.3), Claim (1), page 262, the old circuit has either
the new circuit's length or two more edges. In the latter case
the deleted vertex lies on the old circuit. It is already in
both sides of the old disc separation, so adjoining it does not
raise the order. In both cases X (2.9) therefore selects the
disc separation in the deleted tangle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- The selected inside of the spliced old circuit gives a selected
disc separation in the deleted tangle. This proves the order and
orientation calculation for the hub case of XII (7.3), Claim (1),
page 262. The parameter `n` is the new circuit's length. -/
theorem spliced_circuit_disc_mem_deleted_tangle
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ K C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {v : S} (hv : v ∈ Γ.V)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K)
    {n ε : ℕ} (hε : ε ≤ 1) (hlen : C.length ≤ n + 2 * ε)
    (hvC : ε = 1 → v ∈ C.V) (hshort : n + 2 < 2 * θ) :
    ((PaintingOrDrawing.drawing (deleteVertices Γ {v})).inter (ins C),
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).interOutside (ins C)) ∈
        deleteVerticesTangle Γ.toHypergraph {v} T θ := by
  have hClen : C.length < 2 * θ := by omega
  obtain ⟨hD, hbd, hm⟩ := hins C hC hCK hClen
  have hsepBound := two_mul_disc_separationOrder_le_circuit_length hK hC hCK hbd
  apply selected_disc_mem_deleted_tangle hT hv hD.isClosed hm
  by_cases hεzero : ε = 0
  · have haugBound := separationOrder_adjoin_vertex_le
      ((PaintingOrDrawing.drawing Γ).inter (ins C))
      ((PaintingOrDrawing.drawing Γ).interOutside (ins C)) v
    omega
  · have hεone : ε = 1 := by omega
    have hvfr : v ∈ frontier (ins C) := by
      rw [← subBd_eq_frontier, hbd]
      exact C.V_subset_U (hvC hεone)
    have hvD : v ∈ ins C := hD.isClosed.frontier_subset hvfr
    have hvout : v ∈ closure (univ \ ins C) := by
      rw [frontier_eq_closure_inter_closure] at hvfr
      simpa only [compl_eq_univ_sdiff] using hvfr.2
    have hvSep : v ∈ ((PaintingOrDrawing.drawing Γ).inter (ins C)).vertexSet ∩
        ((PaintingOrDrawing.drawing Γ).interOutside (ins C)).vertexSet :=
      ⟨⟨hv, hvD⟩, hv, hvout⟩
    rw [separationOrder_adjoin_vertex_of_mem hvSep]
    omega

end GraphMinor.GM12
