/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Tactic.NormNum

-- [TABLET NODE: P4638T1FordIncidentCells]

/-!
# P4638T1FordIncidentCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4638T1FordIncidentCells (q1 q2 : Nat) (h1 : 0 < q1) (h2 : 0 < q2)
    (z : GaussianInt)
    (hz : z = 0 ∨ z = -1 ∨ z = -⟨0, 1⟩ ∨ z = -1 - ⟨0, 1⟩) :
    (-(q1 : Int) ≤ z.re ∧ z.re < (q2 : Int) ∧
      0 ≤ z.im ∧ z.im < ((q1 + q2 : Nat) : Int)) ∨
    (-(q2 : Int) ≤ z.re ∧ z.re < (q1 : Int) ∧
      -((q1 + q2 : Nat) : Int) ≤ z.im ∧ z.im < 0) := by
-- BODY
  rcases hz with rfl | rfl | rfl | rfl
  all_goals norm_num
  all_goals omega

end ApollonianSuperharmonic

end
