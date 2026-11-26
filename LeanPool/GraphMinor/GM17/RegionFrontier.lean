/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Sides
import LeanPool.GraphMinor.GM11.PaintingRegions

/-!
# The frontier of a region

Let `r` be a region of a painting and assume that all regions are open discs. A strip along a side
of a cell lies, off the side, in a single region, the region of the side
(`strip_region`). The frontier of a region consists of nodes and of sides of cells
(`frontier_region`), and it is connected (`isPreconnected_frontier`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

variable {Γ : Painting S} [T2Space S]

omit [T2Space S] in
theorem region_subset {r : Set S} (hr : r ∈ Γ.regions) : r ⊆ Γ.Uᶜ := fun _ hx =>
  (arcComponentsIn_subset hr hx).2

omit [T2Space S] in
theorem region_disjoint_closure {r c : Set S} (hr : r ∈ Γ.regions) (hc : c ∈ Γ.C) : Disjoint r
  (closure c) :=
  disjoint_left.mpr fun _ hx hx' => region_subset hr hx (closure_minimal
    (Γ.cell_subset_U hc) Γ.isClosed_U hx')

omit [T2Space S] in
theorem exists_region {x : S} (hx : x ∉ Γ.U) : ∃ r ∈ Γ.regions, x ∈ r :=
  exists_mem_arcComponentsIn (F := univ \ Γ.U) ⟨mem_univ _, hx⟩

omit [T2Space S] in
theorem region_eq {r r' : Set S} (hr : r ∈ Γ.regions) (hr' : r' ∈ Γ.regions) {x : S} (hx : x ∈ r)
  (hx' : x ∈ r') : r = r' :=
  arcComponentsIn_eq_of_mem hr hr' hx hx'

omit [T2Space S] in
/-- A connected set off the paint lies in one region, if regions are open. -/
theorem subset_region (hreg : ∀ r ∈ Γ.regions, IsOpen r) {P : Set S} (hP : IsPreconnected P)
  (hU : Disjoint P Γ.U) {r : Set S} (hr : r ∈ Γ.regions) (hm : (P ∩ r).Nonempty) : P ⊆ r := by
  have hO : IsOpen (⋃ r' ∈ Γ.regions \ {r}, r') := isOpen_biUnion fun r' h => hreg r' h.1
  refine hP.subset_left_of_subset_union (hreg r hr) hO ?_ (fun x hx => ?_) hm
  · refine disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨r', hr', hxr'⟩ := mem_iUnion₂.mp hx'
    exact hr'.2 (region_eq hr'.1 hr hxr' hx)
  · obtain ⟨r', hr', hxr'⟩ := exists_region (Γ := Γ) (disjoint_left.mp hU hx)
    by_cases he : r' = r
    · exact .inl (he ▸ hxr')
    · exact .inr (mem_iUnion₂.mpr ⟨r', ⟨hr', he⟩, hxr'⟩)

omit [T2Space S] in
/-- A disc minus a line of its boundary is connected. -/
theorem isPreconnected_disc_diff {D L : Set S} (hD : IsClosedDisc D) (hL : L ⊆ discBd D) :
  IsPreconnected (D \ L) :=
  hD.isPreconnected_discInt.subset_closure (fun _x hx => ⟨hx.1, fun h => hx.2 (hL h)⟩)
    (sdiff_subset.trans hD.subset_closure_discInt)

omit [T2Space S] in
/-- The part of a strip off its line lies in a single region. -/
theorem strip_region (hreg : ∀ r ∈ Γ.regions, IsOpen r) {L St : Set S} (hSt : IsClosedDisc St)
  (hLb : L ⊆ discBd St) (hSU : St ∩ Γ.U ⊆ L) :
    ∃ r ∈ Γ.regions, St \ L ⊆ r := by
  obtain ⟨φ⟩ := hSt.isOArc_discBd
  obtain ⟨x, hx⟩ : (discInt St).Nonempty :=
    closure_nonempty_iff.mp ⟨_, hSt.subset_closure_discInt (discBd_subset St (φ 1).2)⟩
  have hxU : x ∉ Γ.U := fun h => hx.2 (hLb (hSU ⟨hx.1, h⟩))
  obtain ⟨r, hr, hxr⟩ := exists_region (Γ := Γ) hxU
  refine ⟨r, hr, subset_region hreg (isPreconnected_disc_diff hSt hLb) ?_ hr ⟨x, ⟨hx.1,
    fun h => hx.2 (hLb h)⟩, hxr⟩⟩
  exact disjoint_left.mpr fun y hy hyU => hy.2 (hSU ⟨hy.1, hyU⟩)

omit [T2Space S] in
/-- A region near an inner point of a side is the region of the strip of the side. -/
theorem region_of_strip {c L St r r' : Set S} {y : S} (hc : c ∈ Γ.C) (hLc : L ⊆ closure c)
  (hsub : St \ L ⊆ r) (hr : r ∈ Γ.regions) (hr' : r' ∈ Γ.regions) (hnb : closure c ∪ St ∈ 𝓝 y)
    (hy : y ∈ closure r') : r' = r := by
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff_nhds.mp hy _ hnb
  rcases hzV with h | h
  · exact absurd h (disjoint_left.mp (region_disjoint_closure hr' hc) hz)
  · exact region_eq hr' hr hz (hsub ⟨h, fun hL => disjoint_left.mp (region_disjoint_closure hr' hc)
    hz (hLc hL)⟩)

/-- A strip along a side with its region. -/
theorem side_strip [CompactSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hreg : ∀ r ∈ Γ.regions, IsOpen r) {c L A : Set S} {u v : S}
    (hL : Γ.IsSide c L u v) (hA : IsClosed A) (hAL : A ∩ L ⊆ {u, v}) :
    ∃ St γ r, IsClosedDisc St ∧ IsLineWithEnds γ u v ∧ discBd St = L ∪ γ ∧ L ∩ γ = {u, v}
      ∧ St ∩ closure c = L ∧ St ∩ A ⊆ {u, v} ∧ St ∩ Γ.U ⊆ L ∧
      r ∈ Γ.regions ∧ St \ L ⊆ r ∧ L ⊆ closure r ∧ ∀ x ∈ L, x ≠ u → x ≠ v → closure c ∪ St ∈ 𝓝 x
        := by
  have hbd : ∀ x ∈ L, x ≠ u → x ≠ v → x ∉ bd S := by
    intro x hx hu hv
    exact disjoint_left.mp hL.2 ⟨hx, by rintro (e | e); exacts [hu e, hv e]⟩
  obtain ⟨St, γ, hSt, hγ, hb, hi, hc, hSA, hSU, hnb⟩ :=
    exists_strip hS hL.1.1 hL.1.2.1 hL.1.2.2.1 hbd
      (fun x hx hu hv => hL.1.not_mem_N hx hu hv) hA hAL
  have hLb : L ⊆ discBd St := hb ▸ subset_union_left
  obtain ⟨r, hr, hsub⟩ := strip_region hreg hSt hLb hSU
  refine ⟨St, γ, r, hSt, hγ, hb, hi, hc, hSA, hSU, hr, hsub, ?_, hnb⟩
  have h1 : discInt St ⊆ r := fun x hx => hsub ⟨hx.1, fun h => hx.2 (hLb h)⟩
  exact (hLb.trans (discBd_subset St)).trans (hSt.subset_closure_discInt.trans (closure_mono h1))

/-- The relation between a region and the sides on its frontier. -/
def SideOf (Γ : Painting S) (r L : Set S) : Prop := ∃ c u v, Γ.IsSide c L u v ∧ L ⊆ closure r

/-- The frontier of a region off the nodes lies on sides of this region. -/
theorem frontier_region [CompactSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hreg : ∀ r ∈ Γ.regions, IsOpen r) (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    {r : Set S} (hr : r ∈ Γ.regions) {y : S}
    (hy : y ∈ closure r) (hyr : y ∉ r) (hyN : y ∉ Γ.N) : ∃ L, Γ.SideOf r L ∧ y ∈ L := by
  have hyU : y ∈ Γ.U := by
    by_contra hn
    obtain ⟨r', hr', hyr'⟩ := exists_region (Γ := Γ) hn
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hy r' (hreg r' hr') hyr'
    exact hyr ((region_eq hr' hr hz hz') ▸ hyr')
  obtain ⟨c, hc, hyc⟩ := exists_mem_arcComponentsIn (F := Γ.U \ Γ.N) (x := y) ⟨hyU, hyN⟩
  have hdisc := Γ.isClosedDisc_closure_cell hc
  have hrc := region_disjoint_closure hr hc
  have hycl := subset_closure hyc
  have hyb : y ∈ discBd (closure c) := by
    by_contra hn
    have h1 : y ∈ discInt (closure c) := ⟨hycl, hn⟩
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hy _ (hdisc.isOpen_discInt hS.2.2) h1
    exact disjoint_left.mp hrc hz' hz.1
  have hyS : y ∉ bd S := fun hb => by
    obtain ⟨u, v, -, ht, hB, he, -, -⟩ := Γ.border_cell_exists_ends hc ⟨y, hyc, hb⟩
    have hBs : closure c ∩ bd S ⊆ discBd (closure c) := fun x hx => by
      by_contra hn
      exact hx.2 (isInteriorPoint_of_mem_discInt hS.2.2 hdisc ⟨hx.1, hn⟩)
    have hyi : y ∈ (closure c ∩ bd S) \ {u, v} := he ▸ ⟨hyc, hb⟩
    have hnb := disc_nhds hS hdisc hB hBs rfl hyi.1 (fun e => hyi.2 (.inl e)) (fun e => hyi.2
      (.inr e))
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff_nhds.mp hy _ hnb
    exact disjoint_left.mp hrc hz' hz
  obtain ⟨L, u, v, hL, hyL, hyu, hyv⟩ := exists_side hS hc (h2 c hc) hyb hyN hyS
  obtain ⟨St, γ, r₀, -, -, -, -, -, -, -, hr₀, hsub, hcl, hnb⟩ := side_strip hS hreg hL
    (isClosed_empty) (by simp)
  have he := region_of_strip hc hL.1.subset_closure hsub hr₀ hr (hnb y hyL hyu hyv) hy
  exact ⟨L, ⟨c, u, v, hL, he ▸ hcl⟩, hyL⟩

/-- A side lies on the frontier of one region only. -/
theorem SideOf.unique [CompactSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hreg : ∀ r ∈ Γ.regions, IsOpen r) {r r' L : Set S} (hr : r ∈ Γ.regions)
    (hr' : r' ∈ Γ.regions) (h : Γ.SideOf r L)
    (h' : Γ.SideOf r' L) : r = r' := by
  obtain ⟨c, u, v, hL, hcl⟩ := h
  obtain ⟨c', u', v', hL', hcl'⟩ := h'
  obtain ⟨St, γ, r₀, -, -, -, -, -, -, -, hr₀, hsub, -, hnb⟩ := side_strip hS hreg hL
    (isClosed_empty) (by simp)
  obtain ⟨z, hz, hzu, hzv, -⟩ := exists_inner hL.1.2.1 (finite_empty (α := S))
  rw [region_of_strip hL.1.1 hL.1.subset_closure hsub hr₀ hr (hnb z hz hzu hzv) (hcl hz),
    region_of_strip hL.1.1 hL.1.subset_closure hsub hr₀ hr' (hnb z hz hzu hzv) (hcl' hz)]

end Painting

/-- The ring between a radius and the unit circle in the plane is connected. -/
theorem isPreconnected_ring {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPreconnected {z : EuclideanPlane | ρ < ‖z‖ ∧ ‖z‖ < 1} :=
  GM11.isPreconnected_annulus hρ

/-- The frontier of an open disc in a compact space is connected. -/
theorem isPreconnected_frontier [T2Space S] [CompactSpace S] {r : Set S}
    (hr : IsOpenDisc r) : IsPreconnected (closure r \ r) := by
  simpa only [frontier, hr.1.interior_eq] using GM11.isPreconnected_frontier hr

end GraphMinor.GM17
