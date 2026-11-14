/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5570T1UnitQuadratic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.LinearCombination

/-!
# Quadratic translation from its matrix cocycle

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The explicit unit matrix determines the coefficients in a quadratic cocycle. -/
theorem unitQuadraticTranslation (z x v : GaussianInt) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hmatrix : M = ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)],
      ![(z.im : ℝ), (-z.re : ℝ)]])
    (cocycle : ∃ w : GaussianInt,
      M.mulVec ![(v.re : ℝ), (v.im : ℝ)] = ![(w.re : ℝ), (w.im : ℝ)] ∧
        ∀ y, P5570T1UnitQuadratic z (y + v) = P5570T1UnitQuadratic z y +
          y.re * w.re + y.im * w.im + P5570T1UnitQuadratic z v) :
    P5570T1UnitQuadratic z (x + v) = P5570T1UnitQuadratic z x +
      P5570T1UnitQuadratic z v + ((1 + z.re) * v.re + z.im * v.im) * x.re +
      (z.im * v.re - z.re * v.im) * x.im := by
  obtain ⟨w, hw, hshift⟩ := cocycle
  have hr : (1+z.re)*v.re+z.im*v.im = w.re := by
    have he := congrFun hw 0
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    exact_mod_cast he
  have hi : z.im*v.re-z.re*v.im = w.im := by
    have he := congrFun hw 1
    simp only [hmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at he
    have he' : z.im*v.re + -z.re*v.im = w.im := by exact_mod_cast he
    linear_combination he'
  have he : P5570T1UnitQuadratic z (x+v) =
      P5570T1UnitQuadratic z x + x.re*w.re + x.im*w.im +
        P5570T1UnitQuadratic z v := hshift x
  rw [← hr, ← hi] at he
  linear_combination he

end ApollonianSuperharmonic

end
