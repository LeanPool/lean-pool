/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.GM16.DiscPlaneCoordinates
import LeanPool.GraphMinor.GM16.DrawingTransportIso
import LeanPool.GraphMinor.GM16.DrawingTransportPoints
import LeanPool.GraphMinor.GM16.DrawingBoundaryOrders
import LeanPool.GraphMinor.GM11.Section7

/-!
# A rural presentation of a drawn annulus

Carry the outer closed disc to the plane. The inner disc and all its
boundary points retain their images, so a drawing between these two
discs gives a rural neighborhood. Keep the point-set formula for
subdrawings, so that nested circuits also give a nest in this same
presentation. This is the topological setup of XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u v

/-- A parametrization transports point by point under a map with a
continuous inverse on the containing set. -/
theorem transport_circle_parametrization {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T]
    {D F : Set S} {F' : Set T} {f : S → T} {g : T → S}
    (hf : ContinuousOn f D) (hg : ContinuousOn g (f '' D))
    (hgf : LeftInvOn g f D) (hFD : F ⊆ D) (hF' : F' = f '' F)
    (φ : Circle ≃ₜ F) :
    ∃ φ' : Circle ≃ₜ F', ∀ z, (φ' z).val = f (φ z).val := by
  obtain ⟨e, he⟩ := exists_homeomorph_image (hf.mono hFD)
    (hg.mono (image_mono hFD)) (fun _ hx => hgf (hFD hx))
  exact ⟨φ.trans (e.trans (Homeomorph.setCongr hF'.symm)), fun z => he (φ z)⟩

theorem transport_clockwise_circle_parametrization {S : Type u} [TopologicalSpace S]
    {D F : Set S} {E : Set EuclideanPlane} (hE : IsClosedDisc E) {f : S → EuclideanPlane}
    {g : EuclideanPlane → S} (hf : ContinuousOn f D) (hg : ContinuousOn g (f '' D))
    (hgf : LeftInvOn g f D) (hFD : F ⊆ D) (hbd : subBd E = f '' F) (φ : Circle ≃ₜ F) :
    ∃ (ψ : Circle ≃ₜ F) (ψ' : Circle ≃ₜ subBd E),
      IsClockwiseDiscHomeo E ψ' ∧ ∀ z, (ψ' z).val = f (ψ z).val := by
  obtain ⟨φ', hφ'⟩ := transport_circle_parametrization hf hg hgf hFD hbd φ
  rcases isClockwiseDiscHomeo_or_inv hE rfl φ' with hcw | hcw
  · exact ⟨φ, φ', hcw, hφ'⟩
  · exact ⟨(Homeomorph.inv Circle).trans φ, (Homeomorph.inv Circle).trans φ',
      hcw, fun z => hφ' z⁻¹⟩

variable {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Nonempty S]

/-- A drawing between two closed discs has a rural presentation.
The orders are the orders of its vertices on the two circles. -/
theorem exists_annular_presentation (Q : Drawing S) {D D₀ : Set S}
    (hD : IsClosedDisc D) (hD₀ : IsClosedDisc D₀) (hD₀D : D₀ ⊆ D)
    (hQ : Q.U ⊆ D \ discInt D₀)
    (hne : (Q.V ∩ discBd D).Nonempty) (hne₀ : (Q.V ∩ discBd D₀).Nonempty) :
    ∃ (N : Neighborhood S (Set S)) (P : Presentation N) (f : S → EuclideanPlane),
      N.G = Q.toGraph ∧ N.Ω.bar = Q.V ∩ discBd D ∧
      N.Ω₀.bar = Q.V ∩ discBd D₀ ∧ Continuous f ∧ InjOn f D ∧
      P.Δ = f '' D ∧ P.Δ₀ = f '' D₀ ∧
      (∀ E ⊆ D, IsClosedDisc E →
        IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E) ∧
      ∀ J : Drawing S, J.IsSubdrawing Q →
        graphDrawingSubgraphU P.Γ J.toGraph = f '' J.U := by
  classical
  obtain ⟨f, g, hf, hi, hg, hgf, hdisc⟩ := exists_plane_disc_coordinates hD
  obtain ⟨Γ, hU, hV, hv, he⟩ := exists_graphDrawing_transport Q hf
    (hi.mono (fun _ hx => (hQ hx).1))
  obtain ⟨hΔ, hbd⟩ := hdisc D Subset.rfl hD
  obtain ⟨hΔ₀, hbd₀⟩ := hdisc D₀ hD₀D hD₀
  obtain ⟨φ_orig⟩ := hD.isOArc_discBd
  obtain ⟨φ₀_orig⟩ := hD₀.isOArc_discBd
  obtain ⟨φ, φ', hφ'_cw, hφ'⟩ := transport_clockwise_circle_parametrization hΔ hf.continuousOn hg
    hgf
    (discBd_subset D) hbd φ_orig
  obtain ⟨φ₀, φ₀', hφ₀'_cw, hφ₀'⟩ := transport_clockwise_circle_parametrization hΔ₀ hf.continuousOn
    hg hgf
    ((discBd_subset D₀).trans hD₀D) hbd₀ φ₀_orig
  obtain ⟨Ω, hbar, ha⟩ := exists_drawing_boundary_order Γ hv φ φ' hφ' hne
  obtain ⟨Ω₀, hbar₀, ha₀⟩ := exists_drawing_boundary_order Γ hv φ₀ φ₀' hφ₀' hne₀
  let N : Neighborhood S (Set S) :=
    ⟨Q.toGraph, Ω, Ω₀, Q.finite_V, Q.finite_edges,
      fun _ hx => (hbar ▸ hx).1, fun _ hx => (hbar₀ ▸ hx).1⟩
  have hbetween : Γ.drawing.U ⊆ f '' D \ interior (f '' D₀) := by
    rw [hU]
    rintro _ ⟨x, hxQ, rfl⟩
    have hxD := (hQ hxQ).1
    refine ⟨mem_image_of_mem f hxD, ?_⟩
    intro hxint
    obtain ⟨y, hy, hyx⟩ := interior_subset hxint
    have hyx' : y = x := hi (hD₀D hy) hxD hyx
    have hxD₀ : x ∈ D₀ := hyx' ▸ hy
    have hxnotbd : x ∉ discBd D₀ := by
      intro hxb
      have hfb : f x ∈ subBd (f '' D₀) := hbd₀.symm ▸ mem_image_of_mem f hxb
      rw [subBd_eq_frontier] at hfb
      exact hfb.2 hxint
    exact (hQ hxQ).2 ⟨hxD₀, hxnotbd⟩
  have hiff (E : Set S) (hED : E ⊆ D) (hbdE : subBd (f '' E) = f '' discBd E)
      (x : S) (hx : x ∈ Q.V) :
      graphDrawingVertexSet Γ x ⊆ subBd (f '' E) ↔ x ∈ discBd E := by
    rw [graphDrawingVertexSet_transport Γ hv hx, singleton_subset_iff, hbdE]
    constructor
    · rintro ⟨y, hy, heq⟩
      exact hi (hED (discBd_subset E hy)) (hQ (Q.V_subset_U hx)).1 heq ▸ hy
    · exact mem_image_of_mem f
  let P : Presentation N :=
    ⟨Γ, f '' D, f '' D₀, hΔ, image_mono hD₀D, hbetween,
      fun x hx => (hiff D Subset.rfl hbd x hx).trans
        (by change x ∈ discBd D ↔ x ∈ Ω.bar; rw [hbar]; exact ⟨fun h => ⟨hx, h⟩, And.right⟩),
      fun x hx => (hiff D₀ hD₀D hbd₀ x hx).trans
        (by change x ∈ discBd D₀ ↔ x ∈ Ω₀.bar; rw [hbar₀]; exact ⟨fun h => ⟨hx, h⟩, And.right⟩),
      ⟨φ', hφ'_cw, ha⟩, Or.inr ⟨hΔ₀, φ₀', hφ₀'_cw, ha₀⟩⟩
  refine ⟨N, P, f, rfl, hbar, hbar₀, hf, hi, rfl, rfl, hdisc, ?_⟩
  intro J hJ
  apply graphDrawingSubgraphU_transport Γ hv he _ hJ
  intro e heQ
  apply subset_antisymm
  · exact closure_minimal (image_mono subset_closure)
      ((isClosed_closure.isCompact).image hf).isClosed
  · exact image_closure_subset_closure_image hf

end GraphMinor.GM16
