/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import Mathlib.Init
public import Mathlib.LinearAlgebra.Matrix.Symmetric


/-!
# CircleMatrixSymmetry

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace CircleMatrixSymmetry

/-- Shared symmetric identity for CircleMatrixSymmetry. -/
theorem symmetric :
    (by
      classical
      exact
        ∀ (C : BandCircle), (CircleMatrix C).IsSymm ) := by
  classical
  intro C
  unfold Matrix.IsSymm CircleMatrix
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CircleMatrixSymmetry
end ApollonianSuperharmonic

end
