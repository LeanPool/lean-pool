/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.P3381T1TriangleDeterminant

-- [TABLET NODE: P3523T1SplitDeterminants]

/-!
# P3523T1SplitDeterminants

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3523T1SplitDeterminants (A B C : Real × Real) (u : Real)
    (hu : 0 < u ∧ u < 1)
    (hn : P3381T1TriangleDeterminant ![A, B, C] ≠ 0) :
    let D := (1 - u) • A + u • B
    P3381T1TriangleDeterminant ![A, D, C] =
        u * P3381T1TriangleDeterminant ![A, B, C] ∧
    P3381T1TriangleDeterminant ![D, B, C] =
        (1 - u) * P3381T1TriangleDeterminant ![A, B, C] ∧
    P3381T1TriangleDeterminant ![A, D, C] ≠ 0 ∧
    P3381T1TriangleDeterminant ![D, B, C] ≠ 0 := by
-- BODY
  dsimp only
  have hl : P3381T1TriangleDeterminant ![A, (1 - u) • A + u • B, C] =
      u * P3381T1TriangleDeterminant ![A, B, C] := by
    simp [P3381T1TriangleDeterminant]
    ring
  have hr : P3381T1TriangleDeterminant ![(1 - u) • A + u • B, B, C] =
      (1 - u) * P3381T1TriangleDeterminant ![A, B, C] := by
    simp [P3381T1TriangleDeterminant]
    ring
  exact ⟨hl, hr, hl ▸ mul_ne_zero (ne_of_gt hu.1) hn,
    hr ▸ mul_ne_zero (ne_of_gt (sub_pos.mpr hu.2)) hn⟩

end ApollonianSuperharmonic

end
