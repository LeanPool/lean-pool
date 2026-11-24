/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73EmptyBigon
public import LeanPool.GraphMinor.GM12.Section73DeleteRadialEdge
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Removing empty parallel-spoke discs

For XII (7.3), page 261, minimize the edge count among subdrawings
that retain every vertex, remain two-cell, and have at most one
original drawing edge in each region. If parallel spokes bound a
disc in their original region, an innermost bigon is an empty region.
Delete one boundary edge and merge this empty region with its outside
neighbour. All the conditions persist and the edge count decreases.
Thus the minimum satisfies the no-empty-disc radial condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The finite empty-disc cleanup in Graph Minors XII, (7.3),
page 261. Starting with the radial incidence and hub conditions,
remove spokes until the no-empty-disc condition also holds. Keep
all vertices, the two-cell property, and uniqueness of original
drawing edges within regions. -/
theorem exists_preRadial_subdrawing_by_cleanup
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ H : Drawing S}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell)
    (hcap : Γ.U ∩ H.U = Γ.V) (hV : Γ.V ⊆ H.V)
    (hhub : ∀ r ∈ Γ.R, ∃! w, w ∈ r ∧ w ∈ H.V)
    (hregion : ∀ w ∈ H.V \ Γ.V, ∃ r ∈ Γ.R, w ∈ r)
    (hlink : ∀ e ∈ H.E, ∃ a ∈ Γ.V, ∃ b ∈ H.V \ Γ.V,
      closure e ∩ H.V = {a, b})
    (hunique : ∀ r ∈ H.R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b) :
    ∃ J : Drawing S, J.IsSubdrawing H ∧ J.V = H.V ∧
      (PaintingOrDrawing.drawing J).IsTwoCell ∧
      (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing J ∧
      (∀ r ∈ J.R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b) := by
  classical
  let good : ℕ → Prop := fun n => ∃ J : Drawing S, J.IsSubdrawing H ∧ J.V = H.V ∧
    (PaintingOrDrawing.drawing J).IsTwoCell ∧
    (∀ r ∈ J.R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b) ∧ J.E.ncard = n
  have hex : ∃ n, good n :=
    ⟨H.E.ncard, H, ⟨Subset.rfl, Subset.rfl⟩, rfl, hH, hunique, rfl⟩
  obtain ⟨J, hJH, hJV, hJtwo, hJun, hcount⟩ := Nat.find_spec hex
  have hVJ : Γ.V ⊆ J.V := hJV.symm ▸ hV
  have hcapJ : Γ.U ∩ J.U = Γ.V := by
    apply Subset.antisymm
    · rintro x ⟨hxΓ, hxJ⟩
      exact hcap.subset ⟨hxΓ, hJH.U_subset hxJ⟩
    · intro x hx
      exact ⟨Γ.V_subset_U hx, J.V_subset_U (hVJ hx)⟩
  have hhubJ : ∀ r ∈ Γ.R, ∃! w, w ∈ r ∧ w ∈ J.V := hJV.symm ▸ hhub
  have hregionJ : ∀ w ∈ J.V \ Γ.V, ∃ r ∈ Γ.R, w ∈ r := hJV.symm ▸ hregion
  have hlinkJ : ∀ e ∈ J.E, ∃ a ∈ Γ.V, ∃ b ∈ J.V \ Γ.V,
      closure e ∩ J.V = {a, b} := by
    intro e he
    rw [hJV]
    exact hlink e (hJH.2 he)
  refine ⟨J, hJH, hJV, hJtwo, ⟨hcapJ, hVJ, hhubJ, hregionJ, hlinkJ, ?_⟩, hJun⟩
  intro g hg h hh hgh w hw r hr u hu hcg hch
  rintro ⟨D, hD, hDr, hbdD⟩
  have hwu : w ≠ u := fun h => region_subset hr (h ▸ hu.1) (Γ.V_subset_U hw)
  have hbd : discBd D = closure g ∪ closure h :=
    (GM14.IsClosedDisc.subBd_eq_discBd hS hD).symm.trans hbdD
  have hVD : J.V ∩ D ⊆ {w, u} := by
    rintro x ⟨hxV, hxD⟩
    rcases hDr hxD with hxr | hxw
    · exact Or.inr ((hhubJ r hr).unique ⟨hxr, hxV⟩ ⟨hu.1, hu.2⟩)
    · exact Or.inl hxw
  have hlines : ∀ k ∈ J.E, ∃ a b, IsLineWithEnds (closure k) a b ∧
      closure k ∩ J.V = {a, b} := by
    intro k hk
    obtain ⟨a, ha, b, hb, hck⟩ := hlinkJ k hk
    have hab : a ≠ b := fun h => hb.2 (h ▸ ha)
    exact ⟨a, b, isLine_closure hk hab hck, hck⟩
  obtain ⟨P, a, b, hP, hPD, ha, hb, hab, hca, hcb, hbdP, hPdis, hpreg⟩ :=
    exists_empty_parallel_bigon_region hS hlines hg hh hgh hwu hcg hch hD hbd hVD
  have habd : a ⊆ discBd P := fun x hx => hbdP ▸ Or.inl (subset_closure hx)
  obtain ⟨q, hq, hqp, haq⟩ := exists_region_outside_disc_at_edge hS ha hP habd
  have hap : a ⊆ closure (discInt P) := fun x hx =>
    hP.subset_closure_discInt (Surface.discBd_subset P (habd hx))
  have hnewtwo := isTwoCell_deleteEdge_of_distinct_regions hS hJtwo ha hpreg hq hqp.symm hap haq
  have hdisΓ : ∀ k ∈ Γ.E, Disjoint k J.U := by
    intro k hk
    apply disjoint_left.mpr
    intro x hxk hxJ
    exact (hk.2.1 hxk).2 (hcapJ.subset ⟨(hk.2.1 hxk).1, hxJ⟩)
  have hPr : discInt P ⊆ r := by
    intro x hxP
    rcases hDr (hPD hxP.1) with hxr | hxw
    · exact hxr
    · have hwbd : w ∈ discBd P := hbdP ▸ Or.inl (hca.superset (Or.inl rfl)).1
      exact False.elim (hxP.2 (hxw ▸ hwbd))
  have hempty : ∀ k ∈ Γ.E, ¬ k ⊆ discInt P := by
    intro k hk hkP
    obtain ⟨x, hxk⟩ := hk.1
    exact region_subset hr (hPr (hkP hxk)) (hk.2.1 hxk).1
  have hnewun := region_edge_unique_deleteEdge hS hJtwo ha hpreg hq hqp.symm hap haq hdisΓ hempty
    hJun
  have hnewV : (J.deleteEdge a).V = H.V := (deleteEdge_vertices_eq J a).trans hJV
  have hnewH : (J.deleteEdge a).IsSubdrawing H := (deleteEdge_isSubdrawing J a).trans hJH
  have hgood : good (J.deleteEdge a).E.ncard :=
    ⟨J.deleteEdge a, hnewH, hnewV, hnewtwo, hnewun, rfl⟩
  have hmin : J.E.ncard ≤ (J.deleteEdge a).E.ncard := by
    rw [hcount]
    exact Nat.find_min' hex hgood
  have hlt : (J.deleteEdge a).E.ncard < J.E.ncard := by
    rw [deleteEdge_E]
    exact ncard_lt_ncard ⟨sdiff_subset, fun hback => (hback ha).2 rfl⟩ J.finite_edges
  exact (Nat.not_le_of_gt hlt) hmin

end GraphMinor.GM12
