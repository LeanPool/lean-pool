/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import Mathlib.Init


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

end FordFareySum
end ApollonianSuperharmonic

end
