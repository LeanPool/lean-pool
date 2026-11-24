/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Function

/-!
# Indexing the external path endpoints

XII (4.4), page 251, collects both endpoints of each external path
into the prescribed set. Use an edge index and a Boolean to name
the two ends. Injectivity within each list and disjointness between
the two ranges make all these names distinct.
-/

public section

namespace GraphMinor.GM12

open Set

/-- The paired endpoint indexing is injective when the two endpoint
lists are injective and have disjoint ranges. -/
theorem path_ends_injective
    {ι S : Type*} (s t : ι → S) (hs : Function.Injective s) (ht : Function.Injective t)
    (hdisj : Disjoint (range s) (range t)) :
    Function.Injective (fun q : ι × Bool => if q.2 then s q.1 else t q.1) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ h
  cases c <;> cases d
  · exact Prod.ext (ht h) rfl
  · change t i = s j at h
    exact False.elim (Set.disjoint_left.mp hdisj (mem_range_self j) (h ▸ mem_range_self i))
  · change s i = t j at h
    exact False.elim (Set.disjoint_left.mp hdisj (mem_range_self i) (h.symm ▸ mem_range_self j))
  · exact Prod.ext (hs h) rfl

/-- The paired endpoint names cover precisely both endpoint lists. -/
theorem range_path_ends {ι S : Type*} (s t : ι → S) :
    range (fun q : ι × Bool => if q.2 then s q.1 else t q.1) = range s ∪ range t := by
  ext x
  constructor
  · rintro ⟨⟨i, c⟩, rfl⟩
    cases c
    · exact Or.inr (mem_range_self i)
    · exact Or.inl (mem_range_self i)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨(i, true), rfl⟩
    · exact ⟨(i, false), rfl⟩

end GraphMinor.GM12
