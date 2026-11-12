/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation

-- [TABLET NODE: P3767T1VertexEdgeIncidence]

/-!
# P3767T1VertexEdgeIncidence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3767T1VertexEdgeIncidence {ι : Type} [Nontrivial ι]
    (P : PlaneTriangulation ι) (w : ι) :
    (∃ z, P.adjacent w z) ∧
      ∀ a b, P.adjacent a b → P.position w ∈ P.edgeArc a b →
        w = a ∨ w = b := by
-- BODY
  classical
  have hneighbor : ∃ z, P.adjacent w z := by
    obtain ⟨z, hzw⟩ := exists_ne w
    obtain ⟨p, hp, hl, _, hadj⟩ :=
      P.three_connected ∅ (by simp) w (by simp) z (by simp)
    cases p with
    | nil => simp at hp
    | cons x xs =>
      have hxw : x = w := by simpa using hp
      subst x
      cases xs with
      | nil =>
        have hwz : w = z := by simpa using hl
        exact (hzw hwz.symm).elim
      | cons y ys => exact ⟨y, hadj w y [] ys rfl⟩
  refine ⟨hneighbor, ?_⟩
  intro a b hab hw
  obtain ⟨z, hwz⟩ := hneighbor
  obtain ⟨h, hzero, _⟩ := P.arc_homeomorph w z hwz
  have hw' : P.position w ∈ P.edgeArc w z := by
    rw [← hzero]
    exact (h ⟨0, by norm_num⟩).property
  by_cases heq : ({w, z} : Set ι) = {a, b}
  · have hmem : w ∈ ({a, b} : Set ι) := heq ▸ (by simp)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · have hmem : P.position w ∈
        P.position '' (({w, z} : Set ι) ∩ {a, b}) := by
      rw [← P.arc_intersections w z a b hwz hab heq]
      exact ⟨hw', hw⟩
    obtain ⟨v, hv, hvw⟩ := hmem
    have hvw' : v = w := P.position_injective hvw
    subst v
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv.2

end ApollonianSuperharmonic

end
