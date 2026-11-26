/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RespectAway
public import LeanPool.GraphMinor.GM12.Section72TwoCell
import LeanPool.GraphMinor.GM12.Section72Divert
import LeanPool.GraphMinor.GM12.Section79
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.RadialExists

/-!
# Respectfulness of the restricted tangle in XII (7.2)

Divert every normal circle off the selected disc except at its boundary
vertex, fixing the outside drawing. The diverted circle has precisely
the same vertices and is normal in the original drawing. Pull the
selected inside disc back along the diversion. This follows the
respectfulness paragraph of XII (7.2), page 260, including the case
of a circle through the boundary vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The selected-disc assertion after the diversion in XII (7.2), page 260.
The boundary vertex is not isolated in the outside drawing. -/
theorem theorem_7_2_respectful_of_incident (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {Δ F C : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hC : IsOArc C)
    (hCn : (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsNormal C)
    (hcard : (C ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard < θ)
    (hincident : ∃ e ∈ (Γ.interSet (closure (univ \ Δ))).E, v ∈ closure e) :
    ∃ E : Set S, IsClosedDisc E ∧ subBd E = C ∧
      ((PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).inter E,
        (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).interOutside E) ∈
          restrictTangle T (Γ.interSet (closure (univ \ Δ))).toHypergraph := by
  let Γ' := Γ.interSet (closure (univ \ Δ))
  have hsub : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvb : v ∈ discBd Δ := hdb.symm ▸ hvFV.1
  have hUeq := outside_normal_disc_drawing_U hfr hn
  have hGD : Γ'.U ∩ Δ ⊆ {v} := outside_normal_disc_drawing_inter_subset hfr hn hFV
  have hvnew : v ∈ Γ'.V := (mem_interSet_V_iff isClosed_closure).mpr
    ⟨hvFV.2, by
      have hvfr : v ∈ frontier Δ := hfr.symm ▸ hvFV.1
      rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at hvfr
      exact hvfr.2⟩
  obtain ⟨h, hfix, hpush⟩ := theorem_7_2_divert hS hΔ hvb hvnew hGD hC hCn hincident
  have holdU : ∀ {x}, x ∈ h '' C → x ∈ Γ.U → x ∈ Γ'.U := by
    intro x hxC hxU
    by_cases hxD : x ∈ Δ
    · have hxv : x = v := mem_singleton_iff.mp (hpush ⟨hxC, hxD⟩)
      exact hxv.symm ▸ Γ'.V_subset_U hvnew
    · exact hUeq.symm ▸ ⟨hxU, subset_closure ⟨mem_univ x, hxD⟩⟩
  exact respectful_disc_of_diversion hS hsub hrespect hC hCn hcard h hfix holdU


/-- The respectful-tangle assertion of XII (7.2), pages 259–260. The
outside drawing is two-cell. Its tangle is the order-one restriction,
and every normal circle has the selected disc supplied by diversion. -/
theorem theorem_7_2_respectful (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {Δ F r : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T) :
    IsRespectfulDrawingTangle (Γ.interSet (closure (univ \ Δ))) θ
      (restrictTangle T (Γ.interSet (closure (univ \ Δ))).toHypergraph) := by
  let Γ' := Γ.interSet (closure (univ \ Δ))
  have ht : IsTangle Γ'.toHypergraph θ (restrictTangle T Γ'.toHypergraph) := by
    change IsTangle (Γ.interSet (closure (univ \ Δ))).toHypergraph θ
      (restrictTangle T (Γ.interSet (closure (univ \ Δ))).toHypergraph)
    rw [interSet_toHypergraph Γ isClosed_closure]
    exact theorem_7_1_proof hd.1.2.1 hm (separationOrder_inter_eq_one hΔ.isClosed hbd hFV)
  have htwo := theorem_7_2_twoCell hS hd.1.1 hΔ hbd hn hFV hr hFr
  have hE : Γ'.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le ht hθ
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing hS htwo
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  have hvOld : v ∈ Γ.V := (hFV.symm ▸ mem_singleton v : v ∈ F ∩ Γ.V).2
  have hvNew : v ∈ Γ'.V := by
    apply (mem_interSet_V_iff isClosed_closure).mpr
    refine ⟨hvOld, ?_⟩
    have hvfr : v ∈ frontier Δ := by
      rw [← subBd_eq_frontier, hbd]
      exact (hFV.symm ▸ mem_singleton v : v ∈ F ∩ Γ.V).1
    rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at hvfr
    exact hvfr.2
  have hincident := GM11.exists_edge_of_regionFacts hS hrf hvNew
  refine ⟨htwo, ht, inferInstance, ?_⟩
  intro C hC hCn hcard
  exact theorem_7_2_respectful_of_incident hS hd.1.2.2 hΔ hbd hn hFV hC hCn hcard hincident

end GraphMinor.GM12
