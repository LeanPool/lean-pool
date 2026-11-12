/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import LeanPool.ApollonianSuperharmonic.RealFourNeighborLaplacian

-- [TABLET NODE: QuadraticAffineLaplacian]

/-!
# QuadraticAffineLaplacian

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem QuadraticAffineLaplacian :
    ∀ (A : Matrix (Fin 2) (Fin 2) Real), (A.IsSymm) → (∀ (b : Fin 2 -> Real), ∀ (c : Real), ∀ (x
        : GaussianInt), RealFourNeighborLaplacian
      (fun y => LatticeQuadraticForm A y +
        dotProduct b ![(y.re : Real), (y.im : Real)] + c) x =
      Matrix.trace A) := by
  intro A hA b c x
-- BODY
  simp [RealFourNeighborLaplacian, LatticeQuadraticForm, Matrix.mulVec,
    dotProduct, Matrix.trace]
  ring

end ApollonianSuperharmonic

end
