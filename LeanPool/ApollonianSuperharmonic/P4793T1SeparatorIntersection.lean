/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4793T1SupportingFace

-- [TABLET NODE: P4793T1SeparatorIntersection]

/-!
# P4793T1SeparatorIntersection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1SeparatorIntersection {E : Type*} [AddCommGroup E] [Module Real E]
    (S T : Set E) (f : E →ᵃ[Real] Real)
    (hS : ∀ x ∈ S, 0 ≤ f x) (hT : ∀ x ∈ T, f x ≤ 0)
    (hface : (S ∩ {x | f x = 0} ⊆ T) ∨ (T ∩ {x | f x = 0} ⊆ S)) :
    convexHull Real S ∩ convexHull Real T = convexHull Real (S ∩ T) := by
-- BODY
  have hs := P4793T1SupportingFace S f hS
  have ht := P4793T1SupportingFace T (-f) (by simpa using hT)
  apply Set.Subset.antisymm
  · intro x hx
    have hx0 : f x = 0 := by
      have hn := ht.1 x hx.2
      have hp := hs.1 x hx.1
      change 0 ≤ -f x at hn
      linarith
    rcases hface with hface | hface
    · have hm : x ∈ convexHull Real (S ∩ {x | f x = 0}) := by
        rw [← hs.2]
        exact ⟨hx.1, hx0⟩
      exact convexHull_mono (show S ∩ {x | f x = 0} ⊆ S ∩ T from
        fun y hy => ⟨hy.1, hface hy⟩) hm
    · have hm : x ∈ convexHull Real (T ∩ {x | f x = 0}) := by
        have heq : {x | (-f) x = 0} = {x | f x = 0} := by ext; simp
        rw [← heq, ← ht.2]
        exact ⟨hx.2, by simpa using hx0⟩
      exact convexHull_mono (show T ∩ {x | f x = 0} ⊆ S ∩ T from
        fun y hy => ⟨hface hy, hy.1⟩) hm
  · exact fun x hx => ⟨convexHull_mono Set.inter_subset_left hx,
      convexHull_mono Set.inter_subset_right hx⟩

end ApollonianSuperharmonic

end
