/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P5188T1CeilingBelow]

/-!
# P5188T1CeilingBelow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5188T1CeilingBelow (K E q : Int) (hq : 0 < q) (hE : 0 ≤ E) (hEq : E < q) :
    IntegerCeilDiv (K * q - E) q (by omega) = K := by
-- BODY
  dsimp only [IntegerCeilDiv]
  have he : -(K * q - E) = E + (-K) * q := by ring
  rw [he, show E + (-K) * q = (-K) * q + E by ring,
    Int.mul_add_ediv_right _ _ hq.ne']
  have hdiv : E / q = 0 := Int.ediv_eq_zero_of_lt hE (by omega)
  simp [hdiv]

end ApollonianSuperharmonic

end
