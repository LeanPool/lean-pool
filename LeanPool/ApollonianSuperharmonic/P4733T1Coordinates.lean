/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingData

-- [TABLET NODE: P4733T1Coordinates]

/-!
# P4733T1Coordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1Coordinates {u v : GaussianInt} {L : AddSubgroup GaussianInt}
    (D : P4677T2DrawingData u v L) : Function.Bijective D.coordinates := by
-- BODY
  constructor
  · intro w z h
    apply Subtype.ext
    rw [← D.coordinates_spec w, ← D.coordinates_spec z, h]
  · rintro ⟨m, n⟩
    obtain ⟨r, ⟨hr, w, hw⟩, _⟩ := D.vertex_orbits ⟨.A, m, n⟩
    obtain ⟨hrm, hrn⟩ := (D.vertex_reps r).mp hr
    have hm := congrArg PeriodicSubtileIndex.first hw
    have hn := congrArg PeriodicSubtileIndex.second hw
    simp only [D.shift_eq, hrm, hrn, zero_add] at hm hn
    exact ⟨w, Prod.ext hm.symm hn.symm⟩

end ApollonianSuperharmonic

end
