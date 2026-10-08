/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakProductAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRowClosingAssembly

/-!
# High-contrast homogenization: Provider.Response.PreYoungPartialConstants

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Common coefficients for the pre-Young estimate

The weak-product and boundary-row estimates have distinct dimensional
coefficients.  Their maximum is the component coefficient supplied to the
algebraic pre-Young closure.
-/

namespace HCPolySupport.HighContrast.Response

noncomputable section

/-- The coefficient in the annealed weak-product estimate. -/
@[expose]
def preYoungDivCurlCoefficient (d : ℕ) : ℝ :=
  1 + divCurlDimensionCoeff d * adaptedCutoffDerivativeCoeff d *
    ((51 / 50 : ℝ) * (d : ℝ) ^ 2)

/-- The coefficient left after summing the boundary-row scale weights. -/
@[expose]
def preYoungRowCoefficient (d : ℕ) : ℝ :=
  adaptedCutoffDerivativeCoeff d *
    Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ)))

/-- A common coefficient for the weak-product and boundary-row terms. -/
@[expose]
def preYoungComponentCoefficient (d : ℕ) : ℝ :=
  max (preYoungRowCoefficient d) (preYoungDivCurlCoefficient d)

theorem preYoungRowCoefficient_nonneg (d : ℕ) :
    0 ≤ preYoungRowCoefficient d := by
  exact mul_nonneg (adaptedCutoffDerivativeCoeff_nonneg d)
    (Real.sqrt_nonneg _)

theorem preYoungRowCoefficient_le_component (d : ℕ) :
    preYoungRowCoefficient d ≤ preYoungComponentCoefficient d :=
  le_max_left _ _

theorem preYoungDivCurlCoefficient_le_component (d : ℕ) :
    preYoungDivCurlCoefficient d ≤ preYoungComponentCoefficient d :=
  le_max_right _ _

theorem preYoungComponentCoefficient_nonneg (d : ℕ) :
    0 ≤ preYoungComponentCoefficient d := by
  exact (preYoungRowCoefficient_nonneg d).trans
    (preYoungRowCoefficient_le_component d)

end

end HCPolySupport.HighContrast.Response
