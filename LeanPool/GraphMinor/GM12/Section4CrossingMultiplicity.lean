/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CrossingPoints
import Mathlib.Data.Set.Card

/-!
# Distinct crossings at a noncrossing incident pair

In XII (4.5), page 253, every source vertex has two incident
edges which do not cross each other. Each of those edges has
its own crossing. The crossing points are distinct, since a
common one would be in the two edges' intersection, which is
only their original vertex. In particular the source has at
least two crossings.
-/

public section

namespace GraphMinor.GM12

open Set

/-- A noncrossing incident pair forces at least two source
crossings when every edge has one crossing. This supplies the
nontrivial number of prescribed regions in XII (4.5), page 253. -/
theorem two_le_ncard_meetings_of_noncrossing_pair {V E : Type*}
    (v : V → ℂ) (P : E → Set ℂ) (hM : (edgeMeetingPoints v P).Finite)
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x})
    {w : V} {e f : E} (hinter : P e ∩ P f = {v w}) :
    2 ≤ (edgeMeetingPoints v P).ncard := by
  obtain ⟨x, hxM, hxP⟩ := hcross e
  obtain ⟨y, hyM, hyP⟩ := hcross f
  have hxE : x ∈ P e := (hxP.symm.subset (mem_singleton _)).1
  have hyF : y ∈ P f := (hyP.symm.subset (mem_singleton _)).1
  have hxy : x ≠ y := by
    intro heq
    have hxv : x = v w := mem_singleton_iff.mp (hinter.subset ⟨hxE, heq.symm ▸ hyF⟩)
    obtain ⟨_, _, _, _, hxV⟩ := hxM
    exact hxV ⟨w, hxv.symm⟩
  have hsub : ({x, y} : Set ℂ) ⊆ edgeMeetingPoints v P := by
    rintro z (rfl | rfl)
    · exact hxM
    · exact hyM
  have h := ncard_le_ncard hsub hM
  rwa [ncard_pair hxy] at h

end GraphMinor.GM12
