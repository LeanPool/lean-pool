/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.Section3Main

/-!
# Choosing the dual boundary points for VI (3.6)

The VI (3.6) application in XII (3.2), page 247, needs one point
in each boundary segment between consecutive prescribed vertices.
Choose a point in every segment. Different segments are disjoint,
so the set of chosen points meets each segment exactly once.
When the prescribed vertex set is empty, use the empty set instead.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- A dual point set exists for a boundary and its prescribed
vertices, as needed to apply VI (3.6) in XII (3.2). -/
theorem exists_dual_point_set
    {S : Type*} [TopologicalSpace S] (C V : Set S) :
    ∃ U : Set S, GM06.IsDualPointSet C V U := by
  classical
  by_cases hV : V = ∅
  · refine ⟨∅, fun _ => rfl, ?_⟩
    intro hne
    exact False.elim (hne.ne_empty hV)
  · let I := {s : Set S // s ∈ segmentsOf C V}
    have hex : ∀ s : I, ∃ x, x ∈ s.val := fun s => GM06.segment_nonempty s.property
    choose f hf using hex
    refine ⟨range f, ?_, ?_⟩
    · intro he
      exact False.elim (hV he)
    · intro _
      constructor
      · rintro x ⟨s, rfl⟩
        obtain ⟨⟨a, ha, hsa⟩, _⟩ := s.property
        have hsx := hf s
        rw [← hsa] at hsx
        exact connectedComponentIn_subset _ _ hsx
      · intro s hs
        have hcap : range f ∩ s = {f ⟨s, hs⟩} := by
          apply Subset.antisymm
          · rintro x ⟨⟨t, rfl⟩, hxs⟩
            have hts : t.val = s := by
              by_contra hne
              exact Set.disjoint_left.mp (GM06.disjoint_of_mem_segmentsOf_ne t.property hs hne)
                (hf t) hxs
            have ht : t = (⟨s, hs⟩ : I) := Subtype.ext hts
            exact congrArg f ht
          · intro x hx
            have hxe : x = f (⟨s, hs⟩ : I) := hx
            subst x
            exact ⟨mem_range_self _, hf (⟨s, hs⟩ : I)⟩
        rw [hcap, Set.ncard_singleton]

end GraphMinor.GM12
