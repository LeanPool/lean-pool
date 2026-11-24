/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Compact

/-!
# Pushing a path outside a closed set

The normal-connection construction used by XII (3.1), page 245,
keeps paths outside the deleted disc interiors. Take the first and
last contacts with a closed disc. Since the path ends are outside its
interior, these contacts lie on its frontier. Replace the intervening
part by a path in that frontier. The two remaining outer pieces miss
the interior, and the new carrier uses only the old path and frontier.
-/

public section

namespace GraphMinor.GM12

open Set

private theorem first_contact_not_interior
    {S : Type*} [TopologicalSpace S] {D : Set S} {a b : S} (p : Path a b)
    (ha : a ∉ interior D) {s : unitInterval}
    (hs : IsLeast (p ⁻¹' D) s) : p s ∉ interior D := by
  intro hsi
  by_cases hs0 : s = 0
  · exact ha (by rwa [hs0, p.source] at hsi)
  · have hspos : (0 : unitInterval) < s :=
      lt_of_le_of_ne (unitInterval.nonneg s) (Ne.symm hs0)
    have hscl : s ∈ closure (Iio s) := by
      rw [closure_Iio' (⟨0, hspos⟩ : (Iio s).Nonempty)]
      exact le_rfl
    obtain ⟨t, htO, hts⟩ := mem_closure_iff.mp hscl (p ⁻¹' interior D)
      (isOpen_interior.preimage p.continuous) hsi
    exact hts.not_ge (hs.2 (interior_subset (s := D) htO))

private theorem last_contact_not_interior
    {S : Type*} [TopologicalSpace S] {D : Set S} {a b : S} (p : Path a b)
    (hb : b ∉ interior D) {t : unitInterval}
    (ht : IsGreatest (p ⁻¹' D) t) : p t ∉ interior D := by
  intro hti
  by_cases ht1 : t = 1
  · exact hb (by rwa [ht1, p.target] at hti)
  · have htlt : t < (1 : unitInterval) := lt_of_le_of_ne (unitInterval.le_one t) ht1
    have htcl : t ∈ closure (Ioi t) := by
      rw [closure_Ioi' (⟨1, htlt⟩ : (Ioi t).Nonempty)]
      exact le_rfl
    obtain ⟨s, hsO, hts⟩ := mem_closure_iff.mp htcl (p ⁻¹' interior D)
      (isOpen_interior.preimage p.continuous) hti
    exact hts.not_ge (ht.2 (interior_subset (s := D) hsO))

/-- A path with ends outside the interior of a closed set can be
pushed outside that interior when the frontier is path-connected.
Only frontier points are added to its carrier. -/
theorem exists_path_outside_interior_of_pathConnected_frontier
    {S : Type*} [TopologicalSpace S] {D : Set S} (hD : IsClosed D)
    (hfront : IsPathConnected (frontier D)) {a b : S} (p : Path a b)
    (ha : a ∉ interior D) (hb : b ∉ interior D) :
    ∃ q : Path a b, range q ⊆ range p ∪ frontier D ∧ range q ⊆ (interior D)ᶜ := by
  by_cases hmeet : (p ⁻¹' D).Nonempty
  · obtain ⟨s, hs⟩ := (hD.preimage p.continuous).isCompact.exists_isLeast hmeet
    obtain ⟨t, ht⟩ := (hD.preimage p.continuous).isCompact.exists_isGreatest hmeet
    have hsout := first_contact_not_interior p ha hs
    have htout := last_contact_not_interior p hb ht
    have hsfr : p s ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨hs.1, hsout⟩
    have htfr : p t ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨ht.1, htout⟩
    obtain ⟨m, hm⟩ := hfront.joinedIn (p s) hsfr (p t) htfr
    let q₀ := (p.subpath 0 s).trans (m.trans (p.subpath t 1))
    let q : Path a b := q₀.cast p.source.symm p.target.symm
    have hqr : range q = range (p.subpath 0 s) ∪ (range m ∪ range (p.subpath t 1)) := by
      change range q₀ = _
      rw [Path.trans_range, Path.trans_range]
    have hsub : ∀ r r', range (p.subpath r r') ⊆ range p := by
      intro r r'
      rw [Path.range_subpath]
      exact image_subset_range _ _
    refine ⟨q, ?_, ?_⟩
    · rw [hqr]
      exact union_subset ((hsub 0 s).trans subset_union_left)
        (union_subset ((by rintro _ ⟨z, rfl⟩; exact hm z : range m ⊆ frontier D).trans
          subset_union_right)
          ((hsub t 1).trans subset_union_left))
    · rw [hqr]
      apply union_subset
      · rw [Path.range_subpath_of_le p 0 s (unitInterval.nonneg s)]
        rintro _ ⟨r, hr, rfl⟩ hri
        rcases eq_or_lt_of_le hr.2 with rfl | hrs
        · exact hsout hri
        · exact hrs.not_ge (hs.2 (interior_subset (s := D) hri))
      · apply union_subset
        · rintro _ ⟨r, rfl⟩ hri
          exact (hm r).2 hri
        · rw [Path.range_subpath_of_le p t 1 (unitInterval.le_one t)]
          rintro _ ⟨r, hr, rfl⟩ hri
          rcases eq_or_lt_of_le hr.1 with he | htr
          · exact htout (he.symm ▸ hri)
          · exact htr.not_ge (ht.2 (interior_subset (s := D) hri))
  · refine ⟨p, subset_union_left, ?_⟩
    rintro _ ⟨t, rfl⟩ hti
    exact hmeet ⟨t, interior_subset (s := D) hti⟩

end GraphMinor.GM12
