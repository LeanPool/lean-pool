/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Defs.Basic


-- [TABLET NODE: P3767T1BarrierRegionMaximal]

/-!
# P3767T1BarrierRegionMaximal

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3767T1BarrierRegionMaximal {X : Type} [TopologicalSpace X]
    (U B V : Set X) (hU : IsOpen U) (hfront : frontier U ⊆ B)
    (hV : IsPreconnected V) (havoid : Disjoint V B)
    (hmeet : (V ∩ U).Nonempty) : V ⊆ U := by
-- BODY
  apply hV.subset_left_of_subset_union hU isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr (fun _ hxu hxc => hxc (subset_closure hxu)))
  · intro x hx
    by_cases hxu : x ∈ U
    · exact Or.inl hxu
    · right
      intro hxc
      have hxf : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hxc, hxu⟩
      exact Set.disjoint_left.mp havoid hx (hfront hxf)
  · exact hmeet

end ApollonianSuperharmonic

end
