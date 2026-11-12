/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4715T1Position
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P4715T1PositionInjective]

/-!
# P4715T1PositionInjective

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1PositionInjective : Function.Injective P4715T1Position := by
-- BODY
  rintro ⟨l, m, n⟩ ⟨q, r, s⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change (m : Real) + (P4715T1Offsets l).1 =
    (r : Real) + (P4715T1Offsets q).1 at hx
  change (n : Real) + (P4715T1Offsets l).2 =
    (s : Real) + (P4715T1Offsets q).2 at hy
  have hx' : (12 : Real) * m + 12 * (P4715T1Offsets l).1 =
    12 * r + 12 * (P4715T1Offsets q).1 := by linarith
  have hy' : (12 : Real) * n + 12 * (P4715T1Offsets l).2 =
    12 * s + 12 * (P4715T1Offsets q).2 := by linarith
  cases l <;> cases q <;> norm_num [P4715T1Offsets] at hx' hy'
  all_goals norm_cast at hx' hy'
  all_goals simp_all [PeriodicSubtileIndex.mk.injEq]
  all_goals omega

end ApollonianSuperharmonic

end
