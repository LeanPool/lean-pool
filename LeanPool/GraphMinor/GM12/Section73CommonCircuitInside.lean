/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73SelectedDiscDeletion
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.GM11.Section64
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# The inside of a circuit shared by the two radial drawings

For XII (7.3), Claim (1), page 262, a circuit retained in both
radial drawings has the same selected inside. Its old separation
has order at most half the circuit length. Adding the deleted
vertex to both sides keeps the order small, so the same disc is
selected in the deleted tangle. Two selected discs with the same
boundary agree, since otherwise they cover the surface.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- Two discs with the same radial boundary and selected by the
same pretangle agree. This is the disc-uniqueness argument used
in the inside comparison of XII (7.3), Claim (1), page 262. -/
theorem selected_radial_discs_eq
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : PaintingOrDrawing S} {K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T) (hrad : Γ.U ∩ K.U = Γ.V)
    {D₁ D₂ F : Set S} (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hb₁ : subBd D₁ = F) (hb₂ : subBd D₂ = F) (hFK : F ⊆ K.U)
    (hm₁ : (Γ.inter D₁, Γ.interOutside D₁) ∈ T)
    (hm₂ : (Γ.inter D₂, Γ.interOutside D₂) ∈ T) : D₁ = D₂ := by
  by_contra hne
  have hf₁ : frontier D₁ = F := (subBd_eq_frontier D₁).symm.trans hb₁
  have hf₂ : frontier D₂ = F := (subBd_eq_frontier D₂).symm.trans hb₂
  have hbd : discBd D₁ = discBd D₂ := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hD₁,
      ← IsClosedDisc.frontier_eq_discBd hS hD₂, hf₁, hf₂]
  have hcov := cover_of_discBd_eq hS hD₁ hD₂ hbd hne
  exact not_cover hT hrad hD₁.isClosed hD₂.isClosed hD₁.isClosed
    (hf₁.symm ▸ hFK) (hf₂.symm ▸ hFK) (hf₁.symm ▸ hFK) hm₁ hm₂ hm₁
    (by rw [hcov, univ_union])

/-- The separation at a radial circuit has order at most half its
length. This supplies the order bound in XII (7.3), Claim (1). -/
theorem two_mul_disc_separationOrder_le_circuit_length
    {S : Type*} [TopologicalSpace S]
    {Γ : PaintingOrDrawing S} {K C : Drawing S}
    (hK : Γ.IsPreRadialDrawing K) (hC : C.IsCircuit) (hCs : C.IsSubdrawing K)
    {D : Set S} (hbd : subBd D = C.U) :
    2 * separationOrder (Γ.inter D) (Γ.interOutside D) ≤ C.length := by
  have hf : frontier D = C.U := (subBd_eq_frontier D).symm.trans hbd
  have h₁ := two_mul_ncard_le_length Γ.V (bipartite_of_preRadial hK) hC hCs
  have h₂ : (Γ.V ∩ C.V).Finite := C.finite_V.subset inter_subset_right
  have h₃ := ncard_le_ncard (s := (Γ.inter D ∩ Γ.interOutside D).vertexSet)
    (fun x hx => by
      have hm := inter_outside_vertex hK.2.1 hCs hf hx
      exact ⟨hm.2, hm.1⟩) h₂
  change 2 * (Γ.inter D ∩ Γ.interOutside D).vertexSet.ncard ≤ C.length
  omega

/-- A short circuit shared by the old and new radial drawings has
the same derived inside. This proves the unchanged-circuit case of
XII (7.3), Claim (1), page 262. -/
theorem common_circuit_inside_eq_after_vertex_deletion
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} (hv : v ∈ Γ.V)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J)
    {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) (hCJ : C.IsSubdrawing J)
    (hshort : C.length + 2 < 2 * θ) : ins C = ins' C := by
  obtain ⟨hD, hbd, hm⟩ := hins C hC hCK (by omega)
  have hsepBound := two_mul_disc_separationOrder_le_circuit_length hK hC hCK hbd
  have haugBound := separationOrder_adjoin_vertex_le
    ((PaintingOrDrawing.drawing Γ).inter (ins C))
    ((PaintingOrDrawing.drawing Γ).interOutside (ins C)) v
  have haug : separationOrder
      ((PaintingOrDrawing.drawing Γ).inter (ins C) ∪ vertexHypergraph v)
      ((PaintingOrDrawing.drawing Γ).interOutside (ins C) ∪ vertexHypergraph v) < θ := by omega
  have hmNew := selected_disc_mem_deleted_tangle hT hv hD.isClosed hm haug
  obtain ⟨hD', hbd', hm'⟩ := hins' C hC hCJ (by omega)
  have ht := theorem_7_3_tangle hθ hT hv
  have hpret : IsPretangle (PaintingOrDrawing.drawing (deleteVertices Γ {v})).toHypergraph
      (θ - 1) (deleteVerticesTangle Γ.toHypergraph {v} T θ) :=
    ⟨ht.one_le, ht.isSeparation, ht.order_lt, ht.axiom1, ht.axiom2⟩
  exact selected_radial_discs_eq hS hpret hJ.1 hD hD' hbd hbd' hCJ.U_subset hmNew hm'

end GraphMinor.GM12
