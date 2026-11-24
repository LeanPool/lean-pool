/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Joining two incident vertices through a region

The empty discs of XII (4.3), page 250, start with a normal
arc between two ends of an edge through an incident region.
Approach the region from each end, join the approach points
inside the region, and remove repetitions from the resulting path.
The resulting arc meets the drawing only at its ends.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Distinct vertices incident with one region can be joined by
an arc whose other points lie in that region. -/
theorem exists_arc_through_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {r : Set S} (hr : r ∈ Γ.R)
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) (huv : u ≠ v)
    (hur : u ∈ closure r) (hvr : v ∈ closure r) :
    ∃ a : unitInterval → S, IsArcMap a ∧ a 0 = u ∧ a 1 = v ∧ range a ⊆ r ∪ {u, v} := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨g, hgc, hg0, hgr⟩ := exists_path_into_region hS Γ hu hr hur
  obtain ⟨h, hhc, hh0, hhr⟩ := exists_path_into_region hS Γ hv hr hvr
  let p : Path u (g 1) := ⟨⟨g, hgc⟩, hg0, rfl⟩
  let q : Path v (h 1) := ⟨⟨h, hhc⟩, hh0, rfl⟩
  have hp : JoinedIn (r ∪ {u, v}) u (g 1) := by
    refine ⟨p, ?_⟩
    intro t
    by_cases ht : t = 0
    · exact Or.inr (Or.inl (by change g t = u; rw [ht, hg0]))
    · exact Or.inl (hgr t (lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht)))
  have hq : JoinedIn (r ∪ {u, v}) v (h 1) := by
    refine ⟨q, ?_⟩
    intro t
    by_cases ht : t = 0
    · exact Or.inr (Or.inr (Set.mem_singleton_iff.mpr (by change h t = v; rw [ht, hh0])))
    · exact Or.inl (hhr t (lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht)))
  have hrp : IsPathConnected r := isPathConnected_of_isOpen hS (region_isOpen hr)
    (region_isPreconnected hr) (region_nonempty hr)
  have hmiddle : JoinedIn (r ∪ {u, v}) (g 1) (h 1) :=
    (hrp.joinedIn (g 1) (hgr 1 zero_lt_one) (h 1) (hhr 1 zero_lt_one)).mono subset_union_left
  obtain ⟨w, hw⟩ := hp.trans (hmiddle.trans hq.symm)
  obtain ⟨a, hac, hai, ha0, ha1, har⟩ := exists_arc_of_path w.continuous (by
    rw [w.source, w.target]
    exact huv)
  refine ⟨a, ⟨hac, hai⟩, ha0.trans w.source, ha1.trans w.target, ?_⟩
  intro x hx
  obtain ⟨t, ht⟩ := har hx
  exact ht ▸ hw t

end GraphMinor.GM12
