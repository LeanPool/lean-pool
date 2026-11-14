/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic
public import Mathlib.Init


/-!
# EvenSquareQuotient

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace EvenSquareQuotient

/-- Shared square identity for EvenSquareQuotient. -/
theorem square :
    (by
      classical
      exact
        ∀ (m : ℤ), ((2 : ℤ) * m) ^ (2 : ℕ) / (4 : ℤ) = m ^ (2 : ℕ) ) := by
  classical
  intro m
  have h := P4207T1FloorArithmetic.1 0 m
  simpa using h

end EvenSquareQuotient
end ApollonianSuperharmonic

end
