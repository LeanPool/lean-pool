/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Init
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt


/-!
# RootComplexCoordinates

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace RootComplexCoordinates

/-- Shared lowerGaussianCoordinate identity for RootComplexCoordinates. -/
theorem lowerGaussianCoordinate (a : GaussianInt) : ((1 + 2 * a : GaussianInt) : Complex) = ⟨(2
    * (a.re : Real)) + 1, (2 * (a.im : Real))⟩ := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  change (((1 + 2 * a : GaussianInt) : Complex) = ⟨L + 1, y⟩)
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext <;> simp [Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.im_add, Zsqrtd.im_mul, L, y]; ring

/-- Shared upperGaussianCoordinate identity for RootComplexCoordinates. -/
theorem upperGaussianCoordinate (a : GaussianInt) : ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) :
    Complex) =
      ⟨(2 * (a.re : Real)) + 1, (2 * (a.im : Real)) + 2⟩ := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  change (((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) =
      ⟨L + 1, y + 2⟩)
  rw [GaussianInt.toComplex_def₂]
  apply Complex.ext <;> simp [Zsqrtd.re_add, Zsqrtd.re_mul,
    Zsqrtd.im_add, Zsqrtd.im_mul, L, y]; ring

/-- Shared lowerComplexCoordinate identity for RootComplexCoordinates. -/
theorem lowerComplexCoordinate (a : GaussianInt) : (1 : Complex) + GaussianInt.toComplex (2 :
    GaussianInt) *
      (a : Complex) = ⟨(2 * (a.re : Real)) + 1, (2 * (a.im : Real))⟩ := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  have lowerGaussianCoordinate : ((1 + 2 * a : GaussianInt) : Complex) = ⟨L + 1, y⟩ :=
      lowerGaussianCoordinate a
  change ((1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) = ⟨L + 1, y⟩)
  rw [GaussianInt.toComplex_add, GaussianInt.toComplex_one] at lowerGaussianCoordinate
  rw [GaussianInt.toComplex_mul] at lowerGaussianCoordinate
  exact lowerGaussianCoordinate

/-- Shared upperComplexCoordinate identity for RootComplexCoordinates. -/
theorem upperComplexCoordinate (a : GaussianInt) : (1 : Complex) + GaussianInt.toComplex (2 :
    GaussianInt) *
      (a : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (⟨0, 1⟩ : GaussianInt) = ⟨(2 * (a.re : Real)) + 1, (2 * (a.im : Real)) + 2⟩ := by
  classical
  let L : Real := 2 * (a.re : Real)
  let y : Real := 2 * (a.im : Real)
  have upperGaussianCoordinate : ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex) =
      ⟨L + 1, y + 2⟩ := upperGaussianCoordinate a
  change ((1 : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (a : Complex) + GaussianInt.toComplex (2 : GaussianInt) *
      (⟨0, 1⟩ : GaussianInt) = ⟨L + 1, y + 2⟩)
  rw [GaussianInt.toComplex_add, GaussianInt.toComplex_add,
    GaussianInt.toComplex_one] at upperGaussianCoordinate
  rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_mul] at upperGaussianCoordinate
  exact upperGaussianCoordinate

/-- Shared twoReal identity for RootComplexCoordinates. -/
theorem twoReal : (GaussianInt.toComplex (2 : GaussianInt)).re = 2 := by
  classical
  norm_num [GaussianInt.toComplex_def]

/-- Shared twoImaginary identity for RootComplexCoordinates. -/
theorem twoImaginary : (GaussianInt.toComplex (2 : GaussianInt)).im = 0 := by
  classical
  norm_num [GaussianInt.toComplex_def]

/-- Shared rectangleInterior identity for RootComplexCoordinates. -/
theorem rectangleInterior (l u v w : Real) :
      interior (Set.Icc l u ×ℂ Set.Icc v w) =
        {z : Complex | l < z.re ∧ z.re < u ∧ v < z.im ∧ z.im < w} := by
  classical
  ext z
  simp [Complex.interior_reProdIm, interior_Icc, Complex.mem_reProdIm, Set.mem_Ioo, and_assoc]

/-- Shared sqrtTwentyFive identity for RootComplexCoordinates. -/
theorem sqrtTwentyFive : Real.sqrt (25 : Real) = 5 := by
  classical
  rw [show (25 : Real) = 5 * 5 by norm_num]
  exact Real.sqrt_mul_self (by norm_num)

/-- Shared sqrtSixteen identity for RootComplexCoordinates. -/
theorem sqrtSixteen : Real.sqrt (16 : Real) = 4 := by
  classical
  rw [show (16 : Real) = 4 * 4 by norm_num]
  exact Real.sqrt_mul_self (by norm_num)

end RootComplexCoordinates
end ApollonianSuperharmonic

end
