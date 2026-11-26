/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM11.LeafNbhd
import Mathlib.Topology.Order.Compact

/-!
# Residual edge arcs outside the vertex discs

In XII (4.3), claim (7), page 251, remove the vertex discs
from the drawing and retain an arc for each edge. On the edge
parameter interval, take its last visit to the first closed disc,
then its first visit to the second disc after that. The retained
subarc meets each disc exactly at its corresponding end. Limits
from the intervening interval put these ends on the disc frontiers.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The residual-arc step of XII (4.3), claim (7), page 251.
An arc joining disjoint closed sets has a subarc outside both
sets except for its two frontier ends. -/
theorem exists_residual_arc_between_closed_sets
    {S : Type*} [TopologicalSpace S]
    {a : unitInterval → S} (ha : IsArcMap a) {D E : Set S}
    (hD : IsClosed D) (hE : IsClosed E) (hDE : Disjoint D E)
    (haD : a 0 ∈ D) (haE : a 1 ∈ E) :
    ∃ b : unitInterval → S, IsArcMap b ∧ range b ⊆ range a ∧
      b 0 ∈ frontier D ∧ b 1 ∈ frontier E ∧
      range b ∩ D = {b 0} ∧ range b ∩ E = {b 1} := by
  let A : Set unitInterval := a ⁻¹' D
  have hAc : IsCompact A := (hD.preimage ha.1).isCompact
  have hAne : A.Nonempty := ⟨0, haD⟩
  let t : unitInterval := sSup A
  have ht : IsGreatest A t := hAc.isGreatest_sSup hAne
  have htD : a t ∈ D := ht.1
  have htne : t ≠ 1 := by
    intro heq
    exact Set.disjoint_left.mp hDE htD (heq ▸ haE)
  have ht1 : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) htne
  let F : Set unitInterval := Ici t ∩ a ⁻¹' E
  have hFc : IsCompact F := (isClosed_Ici.inter (hE.preimage ha.1)).isCompact
  have hFne : F.Nonempty := ⟨1, unitInterval.le_one t, haE⟩
  let s : unitInterval := sInf F
  have hs : IsLeast F s := hFc.isLeast_sInf hFne
  have hsE : a s ∈ E := hs.1.2
  have htsne : t ≠ s := by
    intro heq
    exact Set.disjoint_left.mp hDE htD (heq ▸ hsE)
  have hts : t < s := lt_of_le_of_ne hs.1.1 htsne
  have htout : a t ∈ closure Dᶜ := by
    have htcl : t ∈ closure (Ioi t) := by
      rw [closure_Ioi' (a := t) ⟨(1 : unitInterval), ht1⟩]
      exact le_rfl
    apply map_mem_closure ha.1 htcl
    intro z hz hzD
    exact (not_le_of_gt hz) (ht.2 hzD)
  have hsout : a s ∈ closure Eᶜ := by
    have hscl : s ∈ closure (Ioo t s) := by
      rw [closure_Ioo htsne]
      exact ⟨hts.le, le_rfl⟩
    apply map_mem_closure ha.1 hscl
    intro z hz hzE
    exact (not_le_of_gt hz.2) (hs.2 ⟨hz.1.le, hzE⟩)
  have htbd : a t ∈ frontier D := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure htD, htout⟩
  have hsbd : a s ∈ frontier E := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hsE, hsout⟩
  obtain ⟨ρ, hρc, hρi, hρr, hρ0, hρ1⟩ := exists_reparam hts
  let b : unitInterval → S := a ∘ ρ
  have hb0 : b 0 = a t := congrArg a hρ0
  have hb1 : b 1 = a s := congrArg a hρ1
  have hρmem : ∀ z, ρ z ∈ Icc t s := fun z => hρr ▸ mem_range_self z
  refine ⟨b, ⟨ha.1.comp hρc, ha.2.comp hρi⟩, ?_, hb0 ▸ htbd, hb1 ▸ hsbd, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact mem_range_self (ρ z)
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨z, rfl⟩, hzD⟩
      have hzt : ρ z = t := le_antisymm (ht.2 hzD) (hρmem z).1
      exact Set.mem_singleton_iff.mpr ((congrArg a hzt).trans hb0.symm)
    · intro x hx
      have hxb := Set.mem_singleton_iff.mp hx
      exact hxb ▸ ⟨mem_range_self 0, hb0 ▸ htD⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨⟨z, rfl⟩, hzE⟩
      have hzs : ρ z = s := le_antisymm (hρmem z).2 (hs.2 ⟨(hρmem z).1, hzE⟩)
      exact Set.mem_singleton_iff.mpr ((congrArg a hzs).trans hb1.symm)
    · intro x hx
      have hxb := Set.mem_singleton_iff.mp hx
      exact hxb ▸ ⟨mem_range_self 1, hb1 ▸ hsE⟩

end GraphMinor.GM12
