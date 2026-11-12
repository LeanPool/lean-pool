/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P5188T1CeilingShift]

/-!
# P5188T1CeilingShift

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5188T1CeilingShift (M C q : Int) (hq : q ≠ 0) :
    IntegerCeilDiv (M + C * q) q (by omega) =
      IntegerCeilDiv M q (by omega) + C := by
-- BODY
  dsimp only [IntegerCeilDiv]
  have he : -(M + C * q) = (-M) + (-C) * q := by ring
  rw [he, show (-M) + (-C) * q = (-M) + q * (-C) by ring,
    Int.add_mul_ediv_left _ _ hq]
  ring

end ApollonianSuperharmonic

end
