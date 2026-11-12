/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Linarith.Frontend


/-!
# SignSquareProduct

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace SignSquareProduct

/-- Shared product identity for SignSquareProduct. -/
theorem product (σ : ℝ) (hσ : σ ^ 2 = 1) : σ * σ = 1 := by
  classical
  nlinarith [hσ]

end SignSquareProduct
end ApollonianSuperharmonic

end
