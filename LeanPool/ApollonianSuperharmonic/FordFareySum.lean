/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import Mathlib.Init
public import Mathlib.Tactic.Linarith.Frontend



/-!
# FordFareySum

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace FordFareySum

/-- Shared denominatorSum identity for FordFareySum. -/
theorem denominatorSum :
    ∀ (P : FordFareyParameter), P.q = P.q₁ + P.q₂ := by
  classical
  intro P
  exact P.sum_q

/-- Shared determinant fact. -/
theorem determinant :
    ∀ (Q : FordFareyParameter), Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1 := by
  classical
  intro Q
  have h1 : Q.p₁ * ((Q.q₁ + Q.q₂ : Nat) : Int) -
      (Q.q₁ : Int) * (Q.p₁ + Q.p₂) = 1 := by
    simpa [Q.sum_q, Q.sum_p] using Q.det₁
  norm_num [Nat.cast_add] at h1
  nlinarith [h1]

end FordFareySum
end ApollonianSuperharmonic

end
