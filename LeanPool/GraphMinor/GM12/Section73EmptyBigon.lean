/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73InnermostBigon
public import LeanPool.GraphMinor.GM11.Regions
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM12.Section73ImageArc
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# An innermost bigon is an empty region

In the radial cleanup of XII (7.3), page 261, a bigon in a region
has no radial vertices except its two ends. Choose an innermost
parallel-spoke bigon. Any other edge meeting its interior must lie
inside it, have the same two ends, and contradict minimality. The
interior therefore misses the drawing. Its boundary lies in the
drawing, so the interior is one whole region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A loopless edge whose closure lies in a disc containing only
two drawing vertices has exactly those two ends. This identifies
possible interior spokes in the cleanup of XII (7.3), page 261. -/
theorem edge_ends_of_two_vertices_in_disc
    {S : Type*} [TopologicalSpace S] {H : Drawing S} {k Q : Set S} {v u : S}
    (hline : ∃ a b, IsLineWithEnds (closure k) a b ∧ closure k ∩ H.V = {a, b})
    (hVQ : H.V ∩ Q ⊆ {v, u}) (hkQ : closure k ⊆ Q) :
    closure k ∩ H.V = {v, u} := by
  obtain ⟨a, b, hL, hcap⟩ := hline
  have ha := hcap.superset (Or.inl rfl)
  have hb := hcap.superset (Or.inr rfl)
  have haends := hVQ ⟨ha.2, hkQ ha.1⟩
  have hbends := hVQ ⟨hb.2, hkQ hb.1⟩
  have hab := lineWithEnds_ends_ne hL
  rcases haends with hav | hau <;> rcases hbends with hbv | hbu
  · exact False.elim (hab (hav.trans hbv.symm))
  · rw [hcap, hav, hbu]
  · rw [hcap, hau, hbv, pair_comm]
  · exact False.elim (hab (hau.trans hbu.symm))

/-- A parallel-spoke bigon containing only its two end vertices
contains an empty bigon that is a region of the drawing. This gives
a region on which to perform the cleanup in XII (7.3), page 261. -/
theorem exists_empty_parallel_bigon_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S}
    (hlines : ∀ k ∈ H.E, ∃ a b, IsLineWithEnds (closure k) a b ∧
      closure k ∩ H.V = {a, b})
    {g h Q : Set S} {v u : S} (hg : g ∈ H.E) (hh : h ∈ H.E)
    (hgh : g ≠ h) (hvu : v ≠ u)
    (hcg : closure g ∩ H.V = {v, u}) (hch : closure h ∩ H.V = {v, u})
    (hQ : IsClosedDisc Q) (hbd : discBd Q = closure g ∪ closure h)
    (hVQ : H.V ∩ Q ⊆ {v, u}) :
    ∃ (P a b : Set S), IsClosedDisc P ∧ P ⊆ Q ∧ a ∈ H.E ∧ b ∈ H.E ∧
      a ≠ b ∧ closure a ∩ H.V = {v, u} ∧ closure b ∩ H.V = {v, u} ∧
      discBd P = closure a ∪ closure b ∧
      Disjoint (discInt P) H.U ∧ discInt P ∈ H.R := by
  obtain ⟨P, a, b, hP, hPQ, ha, hb, hab, hca, hcb, hbdP, hmin⟩ :=
    exists_innermost_parallel_bigon hg hh hgh hvu hcg hch hQ hbd
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hother : ∀ k ∈ H.E, k ≠ a → k ≠ b → Disjoint k P := by
    intro k hk hka hkb
    have hdisbd : Disjoint k (discBd P) := by
      apply disjoint_left.mpr
      intro x hxk hxbd
      rw [hbdP] at hxbd
      have hxV : x ∈ H.V := by
        rcases hxbd with hxa | hxb
        · exact closure_inter_subset_V hk ha hka ⟨subset_closure hxk, hxa⟩
        · exact closure_inter_subset_V hk hb hkb ⟨subset_closure hxk, hxb⟩
      exact (hk.2.1 hxk).2 hxV
    rcases hP.side hman hk.2.2.1.isConnected.isPreconnected hdisbd with hin | hout
    · have hkP : k ⊆ P := hin.trans (discInt_subset P)
      have hck : closure k ∩ H.V = {v, u} := edge_ends_of_two_vertices_in_disc
        (hlines k hk) hVQ ((closure_minimal hkP hP.isClosed).trans hPQ)
      exact False.elim ((hmin k hk hck hkP).elim hka hkb)
    · exact hout
  have hendsbd : ({v, u} : Set S) ⊆ discBd P := fun x hx =>
    hbdP ▸ Or.inl (hca.superset hx).1
  have hdis : Disjoint (discInt P) H.U := by
    apply disjoint_left.mpr
    intro x hxP hxH
    have hxV : x ∉ H.V := by
      intro hxV
      exact hxP.2 (hendsbd (hVQ ⟨hxV, hPQ hxP.1⟩))
    rw [H.U_eq] at hxH
    rcases hxH with hxV' | hxH
    · exact hxV hxV'
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxH
    by_cases hka : k = a
    · exact hxP.2 (hbdP ▸ Or.inl (hka ▸ hxk))
    · by_cases hkb : k = b
      · exact hxP.2 (hbdP ▸ Or.inr (hkb ▸ hxk))
      · exact disjoint_left.mp (hother k hk hka hkb)
          ((H.closure_diff_V hk).subset ⟨hxk, hxV⟩) hxP.1
  obtain ⟨x, hxP⟩ := hP.nonempty_discInt
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hxP)
  have hPr : discInt P ⊆ r := subset_region hr hP.isPreconnected_discInt hdis hxP hxr
  have hrbd : Disjoint r (discBd P) := by
    apply disjoint_left.mpr
    intro y hyr hybd
    rw [hbdP] at hybd
    rcases hybd with hya | hyb
    · exact region_subset hr hyr (H.closure_subset_U ha hya)
    · exact region_subset hr hyr (H.closure_subset_U hb hyb)
  have hrP : r ⊆ discInt P := by
    rcases hP.side hman (region_isPreconnected hr) hrbd with hin | hout
    · exact hin
    · exact False.elim (disjoint_left.mp hout hxr hxP.1)
  have hregion : discInt P ∈ H.R := (Subset.antisymm hPr hrP) ▸ hr
  exact ⟨P, a, b, hP, hPQ, ha, hb, hab, hca, hcb, hbdP, hdis, hregion⟩

/-- A boundary edge of a disc region has a second incident region
outside that disc. This makes the empty-bigon deletion in XII (7.3),
page 261, a deletion between distinct regions. -/
theorem exists_region_outside_disc_at_edge
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {e P : Set S}
    (he : e ∈ H.E) (hP : IsClosedDisc P) (hebd : e ⊆ discBd P) :
    ∃ q ∈ H.R, q ≠ discInt P ∧ e ⊆ closure q := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x, hxe⟩ := he.1
  obtain ⟨W, A₁, A₂, hW, hxW, _, hcover, hc₁, hc₂, hd₁, hd₂, hcl₁, hcl₂⟩ :=
    exists_edge_sides hS H he hxe
  have hxfr : x ∈ frontier P := (IsClosedDisc.frontier_eq_discBd hS hP).symm ▸ hebd hxe
  have hxcl : x ∈ closure (Pᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hxfr
    exact hxfr.2
  obtain ⟨z, hzW, hzP⟩ := mem_closure_iff.mp hxcl W hW hxW
  obtain ⟨y, hyO, hyH⟩ := exists_notMem_U (Γ := H) hS (hW.inter hP.isClosed.isOpen_compl)
    ⟨z, hzW, hzP⟩
  obtain ⟨q, hq, hyq⟩ := exists_region_of_notMem hyH
  have hxq : x ∈ closure q := by
    rcases hcover ⟨hyO.1, hyH⟩ with hy₁ | hy₂
    · exact closure_mono (subset_region hq hc₁ hd₁ hy₁ hyq) (hcl₁ ⟨hxe, hxW⟩)
    · exact closure_mono (subset_region hq hc₂ hd₂ hy₂ hyq) (hcl₂ ⟨hxe, hxW⟩)
  refine ⟨q, hq, ?_, edge_subset_closure_of_incident hS he hq ⟨x, hxe, hxq⟩⟩
  intro hqP
  exact hyO.2 ((hqP ▸ hyq : y ∈ discInt P).1)

end GraphMinor.GM12
