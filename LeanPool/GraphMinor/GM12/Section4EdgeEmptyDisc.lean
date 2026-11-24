/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section4NormalArcDisc
import LeanPool.GraphMinor.GM12.Section4RegionArc
import LeanPool.GraphMinor.GM12.Section3DiscRegion
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Regions

/-!
# A disc meeting the drawing only at the ends of an edge

XII (4.3), page 250, chooses an empty disc through the two
ends of each free edge. Choose a region incident with the edge,
join its two ends through that region, and thicken the resulting
normal arc. The disc meets that same region, and no other region
meets the disc. This also identifies the incident region needed
for the metric estimate in claim (5).
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The empty-disc choice in XII (4.3), page 250. Its only drawing
points are the two ends, and it meets a region incident with the edge. -/
theorem exists_empty_disc_at_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {e : Set S} {u v : S}
    (hl : Γ.toGraph.IsLink e u v) (huv : u ≠ v) :
    ∃ (D r : Set S), IsClosedDisc D ∧ r ∈ Γ.R ∧ e ⊆ closure r ∧
      Γ.U ∩ D = {u, v} ∧ ({u, v} : Set S) ⊆ discBd D ∧
      Γ.U ∩ D = Γ.V ∩ discBd D ∧ (r ∩ D).Nonempty := by
  obtain ⟨r, hr, her⟩ := exists_region_incident hS hl.edge_mem
  have hue : u ∈ closure e := by
    have h : u ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
    exact h.1
  have hve : v ∈ closure e := by
    have h : v ∈ closure e ∩ Γ.V := by rw [hl.2.2.2]; simp
    exact h.1
  have hcl : closure e ⊆ closure r := closure_minimal her isClosed_closure
  obtain ⟨a, ha, ha0, ha1, har⟩ := exists_arc_through_region hS Γ hr hl.left_mem hl.right_mem huv
    (hcl hue) (hcl hve)
  have hmeet : range a ∩ Γ.U ⊆ {a 0, a 1} := by
    rintro x ⟨hx, hxU⟩
    rcases har hx with hxr | hxends
    · exact False.elim (region_subset hr hxr hxU)
    · simpa only [ha0, ha1] using hxends
  obtain ⟨D, hD, hDU, hends, haD⟩ := exists_normal_arc_disc hS ha Γ.isClosed_U
    (ha0 ▸ Γ.V_subset_U hl.left_mem) (ha1 ▸ Γ.V_subset_U hl.right_mem) hmeet
  have hUD : Γ.U ∩ D = {u, v} := by
    rw [inter_comm]
    simpa only [ha0, ha1] using hDU
  have hbd : ({u, v} : Set S) ⊆ discBd D := by simpa only [ha0, ha1] using hends
  have havoid : Γ.U ∩ D = Γ.V ∩ discBd D := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxends := hUD.subset hx
      refine ⟨?_, hbd hxends⟩
      rcases hxends with rfl | hxends
      · exact hl.left_mem
      · exact (Set.mem_singleton_iff.mp hxends) ▸ hl.right_mem
    · intro x hx
      exact ⟨Γ.V_subset_U hx.1, discBd_subset D hx.2⟩
  let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht0 : t ≠ 0 := by intro h; have h' := congrArg Subtype.val h; norm_num [t] at h'
  have ht1 : t ≠ 1 := by intro h; have h' := congrArg Subtype.val h; norm_num [t] at h'
  have hatr : a t ∈ r := by
    rcases har (mem_range_self t) with h | h
    · exact h
    · rcases h with h | h
      · exact False.elim (ht0 (ha.2 (h.trans ha0.symm)))
      · exact False.elim (ht1 (ha.2 ((Set.mem_singleton_iff.mp h).trans ha1.symm)))
  exact ⟨D, r, hD, hr, her, hUD, hbd, havoid, a t, hatr, haD (mem_range_self t)⟩

end GraphMinor.GM12
