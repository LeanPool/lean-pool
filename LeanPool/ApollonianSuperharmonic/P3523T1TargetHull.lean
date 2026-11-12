/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3523T1InterpolatedTarget

-- [TABLET NODE: P3523T1TargetHull]

/-!
# P3523T1TargetHull

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3523T1TargetHull {r n : Nat}
    {q : P3381T1PolygonBoundary r} {p : P3381T1PolygonBoundary n}
    (s : P3475T1BoundarySubdivision q p)
    {X K : Set (Real × Real)} (t : P3475T1TriangleTree q X K) :
    (∀ i, P3523T1InterpolatedTarget s t (s.start i) = t.target i) ∧
    K = convexHull Real (Set.range (P3523T1InterpolatedTarget s t)) := by
-- BODY
  constructor
  · intro i
    simp [P3523T1InterpolatedTarget, s.edge_start, s.parameter_start]
  · apply Set.Subset.antisymm
    · calc
        K = convexHull Real (Set.range t.target) := t.target_hull
        _ ⊆ convexHull Real (Set.range (P3523T1InterpolatedTarget s t)) := by
          apply convexHull_mono
          rintro _ ⟨i, rfl⟩
          refine ⟨s.start i, ?_⟩
          simp [P3523T1InterpolatedTarget, s.edge_start, s.parameter_start]
    · apply convexHull_min _ t.target_convex
      rintro _ ⟨j, rfl⟩
      have hseg : segment Real (t.target (s.edge j)) (t.target (s.edge j + 1))
          ⊆ K := by
        calc
          segment Real (t.target (s.edge j)) (t.target (s.edge j + 1))
              ⊆ convexHull Real (Set.range t.target) :=
            segment_subset_convexHull ⟨_, rfl⟩ ⟨_, rfl⟩
          _ = K := t.target_hull.symm
      apply hseg
      rw [segment_eq_image]
      exact ⟨s.parameter j,
        ⟨s.parameter_nonneg j, (s.parameter_lt_one j).le⟩, rfl⟩

end ApollonianSuperharmonic

end
