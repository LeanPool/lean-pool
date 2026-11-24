/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2DeformationInside
public import LeanPool.GraphMinor.GM12.Section2BacktrackInside
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section85

/-!
# The two conclusions of the trace deformation

In XII (2.1), Case 1, page 244, the deformed trace is either a
simple circle or a backtracking line. In the circle case its circuit
inside is one of the sets in the walk inside, and region deformation
preserves atom incidence with the selected boundary disc. In the line
case the original boundary contracts in the deformation set. A drawing
point outside the selected disc forces that disc into this set. Every
atom met by the set is met by the deformed trace itself.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A deformation carrier with no new drawing points or region visits
meets only atoms already met by the final curve. -/
theorem atom_meets_image_of_carrier_controls
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {Z : Set S} {ψ : C(Circle, S)}
    (hZΓ : Z ∩ Γ.U ⊆ range ψ)
    (hZR : ∀ r ∈ Γ.R, (Z ∩ r).Nonempty → (range ψ ∩ r).Nonempty)
    {c : Set S} (hc : c ∈ Γ.A) (hcZ : (c ∩ Z).Nonempty) :
    (c ∩ range ψ).Nonempty := by
  obtain ⟨x, hxc, hxZ⟩ := hcZ
  rcases hc with (⟨v, hv, rfl⟩ | he) | hr
  · exact ⟨x, hxc, hZΓ ⟨hxZ, Γ.V_subset_U (hxc ▸ hv)⟩⟩
  · exact ⟨x, hxc, hZΓ ⟨hxZ, (he.2.1 hxc).1⟩⟩
  · obtain ⟨y, hyψ, hyc⟩ := hZR c hr ⟨x, hxZ, hxc⟩
    exact ⟨y, hyc, hyψ⟩

/-- The simple-circle alternative in XII (2.1), Case 1. The circuit
with this circle as point set contributes its selected disc to the
walk inside, and the deformation comparison transfers atom incidence. -/
theorem meets_insWalk_of_embedded_trace_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {φ ψ : C(Circle, S)} (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ)
    (hnφ : Γ.IsNormal (range φ)) {u : S} (W : GraphWalk K.toGraph u u)
    (hshort : W.length < 2 * θ) (hψU : range ψ = (walkDrawing K W).U)
    {D Z c : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = range φ)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hh : ClosedCurvesHomotopicIn Z φ ψ) (hZΓ : Z ∩ Γ.U ⊆ range ψ)
    (hZR : ∀ r ∈ Γ.R, (Z ∩ r).Nonempty → (range ψ ∩ r).Nonempty)
    (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) :
    (c ∩ insWalk ins K W).Nonempty := by
  have hF : IsOArc (range ψ) := ⟨hψ.toHomeomorph⟩
  obtain ⟨C, hC, hCs, hCU⟩ := exists_circuit_of_oArc hF hψU.subset
  have hCK := hCs.trans (walkDrawing_isSubdrawing K W)
  have hCl := isConfined_walk W hshort C hC hCs
  obtain ⟨hE, hbdE, hmE⟩ := hd C hC hCK hCl
  have hnψ : Γ.IsNormal (range ψ) := by
    intro x hx
    have hxK : x ∈ K.U := (walkDrawing_isSubdrawing K W).U_subset (hψU ▸ hx.1)
    exact hK.2.1.1.subset ⟨hx.2, hxK⟩
  have hmeet := atom_meets_disc_of_region_deformation hS hT hφ hψ hD hE hbdD
    (hbdE.trans hCU) hnφ hnψ hmD hmE hh hZΓ hZR hc hcD
  obtain ⟨x, hxc, hxE⟩ := hmeet
  exact ⟨x, hxc, Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCs⟩, hxE⟩)⟩

/-- The line alternative in XII (2.1), Case 1. Contraction in the
controlled carrier puts the selected disc there, and each atom of
that carrier is already met by the trace. -/
theorem meets_insWalk_of_line_trace_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {φ ψ : C(Circle, S)} (hφ : IsEmbedding φ) (hnφ : Γ.IsNormal (range φ))
    {u : S} (W : GraphWalk K.toGraph u u) (hψU : range ψ = (walkDrawing K W).U)
    {D Z L c : Set S} (hD : IsClosedDisc D) (hbdD : subBd D = range φ)
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hh : ClosedCurvesHomotopicIn Z φ ψ) (hL : IsLine L) (hψL : range ψ = L)
    (hZorig : Z ∩ Γ.U ⊆ range φ) (hZΓ : Z ∩ Γ.U ⊆ range ψ)
    (hZR : ∀ r ∈ Γ.R, (Z ∩ r).Nonempty → (range ψ ∩ r).Nonempty)
    (hc : c ∈ Γ.A) (hcD : (c ∩ D).Nonempty) (ins : Drawing S → Set S) :
    (c ∩ insWalk ins K W).Nonempty := by
  have hnDf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbdD]
    exact hnφ
  obtain ⟨q, hqΓ, hqD, _⟩ := exists_support_point_outside_two_small_sides
    (Γ := .drawing Γ) hT hD.isCompact.isClosed hD.isCompact.isClosed hnDf hnDf hmD hmD
  have hφD : range φ ⊆ D := by
    intro x hx
    have hxb : x ∈ subBd D := hbdD.symm ▸ hx
    exact hD.isCompact.isClosed.closure_subset_iff.mpr subset_rfl hxb.1
  have hqZ : q ∉ Z := fun hq => hqD (hφD (hZorig ⟨hq, hqΓ⟩))
  have hψZ : range ψ ⊆ Z := by
    obtain ⟨H, hHZ, _, hH1⟩ := hh
    rintro x ⟨z, rfl⟩
    exact hH1 z ▸ hHZ (z, 1)
  have hLZ : L ⊆ Z := hψL ▸ hψZ
  have hn : ClosedCurveIsNullHomotopicIn Z φ := GM11.null_of_homotopic hLZ hh
    ((GM11.IsLine.isSimplyConnected hL).2 ψ hψL.subset)
  have hDZ : D ⊆ Z := by
    intro p hpD
    by_contra hpZ
    have hZpair : Z ⊆ ({p, q} : Set S)ᶜ := by
      intro x hx hpair
      simp only [mem_insert_iff, mem_singleton_iff] at hpair
      rcases hpair with hxp | hxq
      · exact hpZ (hxp ▸ hx)
      · exact hqZ (hxq ▸ hx)
    obtain ⟨z, hz, H⟩ := hn
    have hnpair : ClosedCurveIsNullHomotopicIn ({p, q} : Set S)ᶜ φ := ⟨z, hZpair hz, H.mono hZpair⟩
    exact ((curve_null_in_pair_compl_iff_not_mem_disc hS hφ hD hbdD hqD).mp hnpair) hpD
  obtain ⟨x, hxc, hxψ⟩ := atom_meets_image_of_carrier_controls hZΓ hZR hc
    (hcD.mono (inter_subset_inter_right c hDZ))
  exact ⟨x, hxc, Or.inl (hψU ▸ hxψ)⟩

end GraphMinor.GM12
