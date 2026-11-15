/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Affine coordinates in the real plane

Shared coordinate maps and inverse laws adapted from Wesley Pegden's Apache-2.0 formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace PlaneAffineCoordinates

/-- The plane vector with the given coordinates in an ordered pair of vectors. -/
noncomputable abbrev linear (first second point : Real × Real) : Real × Real :=
  (point.1 * first.1 + point.2 * second.1, point.1 * first.2 + point.2 * second.2)

/-- Coordinates in an ordered pair of vectors, using the determinant formula. -/
noncomputable abbrev inverse (first second point : Real × Real) : Real × Real :=
  let determinant := first.1 * second.2 - first.2 * second.1
  ((point.1 * second.2 - point.2 * second.1) / determinant,
    (first.1 * point.2 - first.2 * point.1) / determinant)

/-- The coordinate formula inverts reconstruction for a nondegenerate ordered pair. -/
theorem inverse_linear (first second point : Real × Real)
    (nonzero : first.1 * second.2 - first.2 * second.1 ≠ 0) :
    inverse first second (linear first second point) = point := by
  dsimp [linear, inverse]
  have reordered : first.1 * second.2 - second.1 * first.2 ≠ 0 := by
    simpa [mul_comm] using nonzero
  apply Prod.ext <;> field_simp [reordered] <;> ring

/-- Reconstruction inverts the coordinate formula for a nondegenerate ordered pair. -/
theorem linear_inverse (first second point : Real × Real)
    (nonzero : first.1 * second.2 - first.2 * second.1 ≠ 0) :
    linear first second (inverse first second point) = point := by
  dsimp [linear, inverse]
  have reordered : second.2 * first.1 - second.1 * first.2 ≠ 0 := by
    simpa [mul_comm] using nonzero
  apply Prod.ext <;> field_simp [reordered] <;> ring

/-- The affine plane chart determined by an origin and a nondegenerate ordered pair. -/
noncomputable abbrev homeomorphism (origin first second : Real × Real)
    (nonzero : first.1 * second.2 - first.2 * second.1 ≠ 0) :
    (Real × Real) ≃ₜ (Real × Real) :=
  { toFun := fun point => origin + linear first second point
    invFun := fun point => inverse first second (point - origin)
    left_inv := fun point => by simp [inverse_linear, nonzero]
    right_inv := fun point => by simp [linear_inverse, nonzero]
    continuous_toFun := by dsimp [linear]; fun_prop
    continuous_invFun := by dsimp [inverse]; fun_prop }

end PlaneAffineCoordinates
end ApollonianSuperharmonic

end
