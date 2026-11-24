/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Radial
import LeanPool.GraphMinor.GM12.Section72Tangle
import LeanPool.GraphMinor.GM11.Section810

/-!
# A radial subdrawing for the original disc restriction

In XII (7.2), page 260, the two-spoke trace either backtracks, in
which case no old drawing point is removed, or gives a boundary
circuit with the same old inside and outside. In the second case use
the proved radial deletion. In both cases the new radial drawing is
a subdrawing of the old one and retains the old region's hub.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- Restriction to a closed set containing the whole drawing leaves
the drawing unchanged. -/
theorem interSet_eq_self_of_U_subset {Γ : Drawing S} {X : Set S}
    (hX : IsClosed X) (hΓX : Γ.U ⊆ X) : Γ.interSet X = Γ := by
  apply Drawing.ext_of_V_E
  · ext x
    rw [mem_interSet_V_iff hX]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hΓX (Γ.V_subset_U hx)⟩⟩
  · ext e
    rw [mem_interSet_E_iff]
    exact ⟨fun he => he.1, fun he => ⟨he, fun x hx => hΓX (he.2.1 hx).1⟩⟩

/-- The radial subdrawing and retained hub used in the metric
comparisons of XII (7.2), page 260, for the original boundary disc. -/
theorem exists_radial_subdrawing_after_disc_deletion [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T) (hθ : 2 ≤ θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {F r D : Set S} {v : S} (hF : IsOArc F) (hvF : v ∈ F)
    (hv : v ∈ Γ.V) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hn : Γ.IsNormal F) (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    ∃ K' : Drawing S,
      (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ D)))).IsRadialDrawing K' ∧
      K'.IsSubdrawing K ∧ ∃ u ∈ r, u ∈ K'.V := by
  rcases exists_radial_boundary_circuit_or_disc_subset_region hS hT hθ hK hE hd
      hF hvF hv hr hFr hn hD hbd hm with hDZ | hcircle
  · have hΓX : Γ.U ⊆ closure (univ \ D) := by
      intro x hxΓ
      by_cases hxD : x ∈ D
      · rcases hDZ hxD with hxr | hxv
        · exact (region_subset hr hxr hxΓ).elim
        · have hxf : x ∈ frontier D := by
            rw [← subBd_eq_frontier, hbd]
            exact mem_singleton_iff.mp hxv ▸ hvF
          rw [frontier_eq_closure_inter_closure] at hxf
          simpa only [compl_eq_univ_sdiff] using hxf.2
      · exact subset_closure ⟨mem_univ _, hxD⟩
    have hΓeq := interSet_eq_self_of_U_subset isClosed_closure hΓX
    obtain ⟨u, hu, _⟩ := hK.2.1.2.2.1 r hr
    refine ⟨K, ?_, Drawing.IsSubdrawing.refl K, u, hu.1, hu.2⟩
    rw [hΓeq]
    exact hK
  · obtain ⟨C, hC, hCK, hlen, _, _, hout, hCZ, hmeet⟩ := hcircle
    obtain ⟨hDC, hbdC, _⟩ := hd C hC hCK (by omega)
    obtain ⟨u, e, f, hu, hef, hCE, he, hf⟩ :=
      two_spokes_of_radial_boundary hK.2.1 hCK hlen hr hCZ hmeet
    obtain ⟨hCV, hCU⟩ := two_spoke_circuit_point_sets hC hCK hCE he hf
    have hfrontC : frontier (ins C) = C.U := (subBd_eq_frontier _).symm.trans hbdC
    have hΓeq : Γ.interSet (closure (univ \ D)) = Γ.interSet (closure (univ \ ins C)) := by
      have hHG : (Γ.interSet (closure (univ \ D))).toHypergraph =
          (Γ.interSet (closure (univ \ ins C))).toHypergraph := by
        rw [interSet_toHypergraph Γ isClosed_closure, interSet_toHypergraph Γ isClosed_closure]
        exact hout
      exact Drawing.ext_of_V_E (congrArg Hypergraph.vertexSet hHG) (congrArg Hypergraph.edgeSet hHG)
    have hRad := radialDiscDeletion_isRadial hS hK hCK hDC hfrontC hCE hCV hef hCU hCZ
      he hf hmeet hr hv hu.1 hu.2
    have huNew : u ∈ (radialDiscDeletion K (ins C) f).V := by
      have huf : u ∈ frontier (ins C) := hfrontC.symm ▸ C.V_subset_U (hCV.symm ▸ Or.inr rfl)
      rw [frontier_eq_closure_inter_closure] at huf
      rw [radialDiscDeletion_V]
      exact ⟨hu.2, by simpa only [compl_eq_univ_sdiff] using huf.2⟩
    refine ⟨radialDiscDeletion K (ins C) f, ?_, radialDiscDeletion_isSubdrawing K (ins C) f,
      u, hu.1, huNew⟩
    rw [hΓeq]
    exact hRad

end GraphMinor.GM12
