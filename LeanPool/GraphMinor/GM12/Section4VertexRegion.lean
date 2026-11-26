/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# A short normal arc leaving a drawing vertex

For XII (4.4), page 251, the small disc at a selected vertex starts
with an arc leaving that vertex through an incident region. Region
closures cover the surface because there are finitely many regions
and the drawing has empty interior. Restrict the region-entry path
to a short initial interval inside the assigned open neighborhood,
then remove repetitions.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 Metric

/-- Region closures cover a drawing in a closed surface. -/
theorem exists_region_at_point
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (x : S) :
    ∃ r ∈ Γ.R, x ∈ closure r := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hx : x ∈ closure (⋃₀ Γ.R) := by
    apply _root_.mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ) hS hO ⟨x, hxO⟩
    obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
    exact ⟨y, hyO, r, hr, hyr⟩
  rw [(finite_R hS Γ).closure_sUnion] at hx
  obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
  exact ⟨r, hr, hxr⟩

/-- Leave a vertex along an arc that stays in an assigned open set
and meets the drawing only at that vertex. -/
theorem exists_normal_arc_from_vertex_in_open
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {v : S} (hv : v ∈ Γ.V)
    {U : Set S} (hU : IsOpen U) (hvU : v ∈ U) :
    ∃ a : unitInterval → S, IsArcMap a ∧ a 0 = v ∧ a 1 ∉ Γ.U ∧
      range a ⊆ U ∧ range a ∩ Γ.U = {v} := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨r, hr, hvr⟩ := exists_region_at_point hS Γ v
  obtain ⟨g, hgc, hg0, hgr⟩ := exists_path_into_region hS Γ hv hr hvr
  have hgU : g 0 ∈ U := hg0.symm ▸ hvU
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hgc.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU))
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let f : unitInterval → unitInterval := fun t =>
    ⟨δ * t.val, mul_nonneg hδ.le t.property.1,
      (mul_le_mul_of_nonneg_left t.property.2 hδ.le).trans (by simpa using hδ1)⟩
  have hfc : Continuous f := (show Continuous (fun t : unitInterval => δ * t.val) by
    fun_prop).subtype_mk _
  have hf0 : f 0 = 0 := by apply Subtype.ext; change δ * 0 = 0; exact mul_zero _
  let b : unitInterval → S := fun t => g (f t)
  have hbc : Continuous b := hgc.comp hfc
  have hb0 : b 0 = v := by change g (f 0) = v; rw [hf0, hg0]
  have hbU : ∀ t, b t ∈ U := by
    intro t
    apply hεsub
    change dist (δ * t.val) (0 : ℝ) < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hδ.le t.property.1)]
    exact (mul_le_mul_of_nonneg_left t.property.2 hδ.le).trans_lt (by simpa using hδε)
  have hbnot : ∀ t, t ≠ 0 → b t ∉ Γ.U := by
    intro t ht
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1
      (fun h => ht (Subtype.ext h.symm))
    exact region_subset hr (hgr (f t) (show 0 < f t from mul_pos hδ htpos))
  have hb1 : b 1 ∉ Γ.U := hbnot 1 one_ne_zero
  have hneq : b 0 ≠ b 1 := fun heq => hb1 (heq ▸ (hb0.symm ▸ Γ.V_subset_U hv))
  obtain ⟨a, hac, hai, ha0, ha1, hab⟩ := exists_arc_of_path hbc hneq
  refine ⟨a, ⟨hac, hai⟩, ha0.trans hb0, ?_, ?_, ?_⟩
  · rw [ha1]
    exact hb1
  · rintro x hx
    obtain ⟨t, rfl⟩ := hab hx
    exact hbU t
  · apply Set.Subset.antisymm
    · rintro x ⟨hx, hxΓ⟩
      obtain ⟨t, htx⟩ := hab hx
      by_cases ht : t = 0
      · exact Set.mem_singleton_iff.mpr (htx.symm.trans (ht ▸ hb0))
      · exact False.elim (hbnot t ht (htx.symm ▸ hxΓ))
    · rintro x rfl
      exact ⟨⟨0, ha0.trans hb0⟩, Γ.V_subset_U hv⟩

end GraphMinor.GM12
