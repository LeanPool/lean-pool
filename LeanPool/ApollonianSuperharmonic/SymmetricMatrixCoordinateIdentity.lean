/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SymmetricMatrixCoordinates

-- [TABLET NODE: SymmetricMatrixCoordinateIdentity]

/-!
# SymmetricMatrixCoordinateIdentity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SymmetricMatrixCoordinateIdentity
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm) :
    let x := SymmetricMatrixCoordinates A
    A = (2 : Real)⁻¹ •
      ![![x.2 + x.1.re, x.1.im], ![x.1.im, x.2 - x.1.re]] := by
-- BODY
  dsimp [SymmetricMatrixCoordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, smul_eq_mul, hA.apply 0 1] <;> ring

end ApollonianSuperharmonic

end
