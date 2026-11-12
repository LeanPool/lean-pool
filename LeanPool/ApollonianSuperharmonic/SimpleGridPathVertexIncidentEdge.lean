/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: SimpleGridPathVertexIncidentEdge]

/-!
# SimpleGridPathVertexIncidentEdge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SimpleGridPathVertexIncidentEdge
    (V : Set GaussianInt) (E : Set (Finset GaussianInt))
    (hpath : SimpleGridPath V E) (x : GaussianInt) (hx : x ∈ V) :
    ∃ e : Finset GaussianInt, x ∈ e ∧ e ∈ E := by
-- BODY
  rcases hpath with ⟨p, hp, hlen, hV, hstep, hE⟩
  have hxlist : x ∈ p := by
    rw [hV] at hx
    simpa using hx
  have split_mem : ∀ (r : List GaussianInt) (z : GaussianInt),
      z ∈ r → ∃ l t, r = l ++ z :: t := by
    intro r z hz
    induction r with
    | nil => simp at hz
    | cons q r ih =>
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨[], r, rfl⟩
      · rcases ih hz with ⟨l, t, ht⟩
        exact ⟨q :: l, t, by simp [ht, List.cons_append]⟩
  rcases split_mem p x hxlist with ⟨l, t, hsplit⟩
  by_cases ht : t = []
  · subst t
    have hl : l ≠ [] := by
      intro hl
      subst l
      rw [hsplit] at hlen
      simp at hlen
    let z := l.getLast hl
    let l₀ := l.dropLast
    have hlt : l₀ ++ [z] = l := List.dropLast_append_getLast hl
    refine ⟨{z, x}, by simp, (hE {z, x}).2 ?_⟩
    refine ⟨z, x, l₀, [], ?_, rfl⟩
    rw [← hlt] at hsplit
    simpa [List.append_assoc] using hsplit
  · obtain ⟨z, t₀, rfl⟩ := List.exists_cons_of_ne_nil ht
    refine ⟨{x, z}, by simp, (hE {x, z}).2 ?_⟩
    exact ⟨x, z, l, t₀, hsplit, rfl⟩

end ApollonianSuperharmonic

end
