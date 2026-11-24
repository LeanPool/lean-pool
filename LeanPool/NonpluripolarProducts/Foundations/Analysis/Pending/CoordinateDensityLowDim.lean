/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# The exterior-power/determinant density identity in low dimension

The general identity between the genuine exterior-power coefficient and the
complex determinant is a finite shuffle computation.  This file establishes
its base dimensions.  In complex dimension one no type `(1,1)` hypothesis is
needed: alternatingness kills the second real term in
`normalizedHermitianMatrix`, and the remaining complex factors cancel exactly.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-- In complex dimension zero both normalizations use the empty-product unit. -/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_zero
    (A : CoordinateRealTwoForm 0) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  simp [actualTopPowerDensity_zero, normalizedTopPowerDensity, complexTopCoefficient]

/-- In complex dimension one, the genuine top exterior power and the
normalized determinant coefficient agree for every real alternating two-form. -/
theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_one
    (A : CoordinateRealTwoForm 1) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  rw [actualTopPowerDensity_one]
  have hself : A ![coordinateVector (0 : Fin 1), coordinateVector (0 : Fin 1)] = 0 := by
    exact A.map_eq_zero_of_eq ![coordinateVector (0 : Fin 1), coordinateVector (0 : Fin 1)]
      (i := 0) (j := 1) (by rfl) (by decide)
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hcancel (x : ℝ) :
      Complex.I / (2 * (Real.pi : ℂ)) * ((Real.pi : ℂ) * (x : ℂ)) *
          (-2 * Complex.I) = (x : ℂ) := by
    field_simp [hpi]
    rw [Complex.I_sq]
    ring
  simp only [normalizedTopPowerDensity, complexTopCoefficient, Nat.factorial_one,
    Nat.cast_one, one_mul, pow_one, Matrix.det_fin_one, normalizedHermitianMatrix,
    hself, Complex.ofReal_zero, mul_zero, sub_zero]
  rw [hcancel]
  rfl

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
