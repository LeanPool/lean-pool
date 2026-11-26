/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section7

/-!
# Zero-length traces

The zero-length case of XII (2.1), pages 243--244, needs a separate
argument. The curve lies in one region. Any circle in its image bounds
a disc inside that region. This is also the disc selected by the tangle:
a different disc with the same boundary would contain the whole drawing,
contrary to the third tangle condition. The only atom meeting the disc
is that region, which contains the zero-length trace vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 Hypergraph

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- A normal curve of length zero has the zero-edge trace from the
unique radial vertex of its region, as defined in XII, page 243. -/
theorem exists_trace_of_length_zero {Γ K : Drawing S} {φ : C(Circle, S)}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hφ : IsNormalCurve Γ φ) (hzero : curveLength Γ φ = 0) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u), IsTrace Γ K φ W := by
  have hemp : {x | φ x ∈ Γ.U} = ∅ := (Set.ncard_eq_zero hφ.1).mp hzero
  have hoff : ∀ x, φ x ∉ Γ.U := by
    intro x hx
    exact Set.notMem_empty x (hemp ▸ hx)
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (hoff 1)
  have hsub : range φ ⊆ r := subset_region hr
    (isPreconnected_range φ.continuous) (Set.disjoint_left.mpr (by rintro y ⟨x, rfl⟩; exact hoff x))
    ⟨1, rfl⟩ hxr
  obtain ⟨u, ⟨hur, huK⟩, _⟩ := hK.2.1.2.2.1 r hr
  exact ⟨u, .nil huK, hφ, Or.inl ⟨hzero, rfl, huK, r, hr, hsub, hur⟩⟩

omit [T1Space S] in
/-- An atom meeting a region is that region, since distinct atoms
are disjoint. Used in the zero and backtracking cases of XII (2.1). -/
theorem atom_eq_region_of_meets {Γ : Drawing S} {c r : Set S}
    (hc : c ∈ Γ.A) (hr : r ∈ Γ.R) (hcr : (c ∩ r).Nonempty) : c = r := by
  obtain ⟨x, hxc, hxr⟩ := hcr
  rcases hc with (⟨v, hv, rfl⟩ | hc) | hc
  · exact (region_subset hr hxr (Γ.V_subset_U (mem_singleton_iff.mp hxc ▸ hv))).elim
  · exact (region_subset hr hxr (hc.2.1 hxc).1).elim
  · exact region_eq_of_mem hc hr hxc hxr

omit [T1Space S] in
/-- A tangle-selected disc bounded by a circle in a region lies inside
that region. Choosing the other disc would put every drawing vertex
on the small side. This supplies the zero-length case of XII (2.1). -/
theorem selected_disc_subset_region [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) {r F Δ : Set S}
    (hr : r ∈ Γ.R) (hcell : IsOpenDisc r) (hF : IsOArc F) (hFr : F ⊆ r)
    (hΔ : IsClosedDisc Δ) (hb : subBd Δ = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T) : Δ ⊆ r := by
  obtain ⟨D, hDr, hD, hbd⟩ := exists_disc_in_openDisc hcell hF hFr
  have hbdΔ : discBd Δ = F := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hΔ, ← subBd_eq_frontier]
    exact hb
  by_cases heq : Δ = D
  · exact heq ▸ hDr
  have hcov : Δ ∪ D = univ := cover_of_discBd_eq hS hΔ hD (hbdΔ.trans hbd.symm) heq
  exfalso
  apply hT.axiom3 hm
  ext x
  change (x ∈ Γ.V ∧ x ∈ Δ) ↔ x ∈ Γ.V
  refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
  have hxUD : x ∈ Δ ∪ D := hcov ▸ mem_univ x
  exact hxUD.resolve_right (fun hxD => region_subset hr (hDr hxD) (Γ.V_subset_U hx))

/-- Graph Minors XII, (2.1), zero-length case, pages 243--244. Every
atom meeting a tangle-selected disc bounded by a circle in the curve's
image meets the inside of the trace. -/
theorem theorem_2_1_zero [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T)
    (hcell : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    {φ : C(Circle, S)} {u : S} {W : GraphWalk K.toGraph u u}
    (hW : IsTrace Γ K φ W) (hzero : curveLength Γ φ = 0)
    {ins : Drawing S → Set S} {F Δ c : Set S}
    (hF : IsOArc F) (hFφ : F ⊆ range φ) (hΔ : IsClosedDisc Δ)
    (hb : subBd Δ = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    (hc : c ∈ Γ.A) (hcΔ : (c ∩ Δ).Nonempty) :
    (c ∩ insWalk ins K W).Nonempty := by
  rcases hW.2 with h | h
  · obtain ⟨_, _, _, r, hr, hφr, hur⟩ := h
    have hΔr := selected_disc_subset_region hS hT hr (hcell.2 r hr) hF
      (hFφ.trans hφr) hΔ hb hm
    have hcr : c = r := atom_eq_region_of_meets hc hr
      (hcΔ.mono (inter_subset_inter_right c hΔr))
    refine ⟨u, hcr.symm ▸ hur, Or.inl ?_⟩
    apply (walkDrawing K W).V_subset_U
    rw [walkDrawing_V]
    exact W.start_mem_support
  · exact (Nat.ne_of_gt h.1 hzero).elim

end GraphMinor.GM12
