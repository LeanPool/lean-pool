/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenHeadClassSplit

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.RateFactorToHoleShape

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rate factor, from the capstone's shape to the hole's

that module concludes at the capstone's own length `x · eccentricityFoldFactor abar p₀`
and at whatever constant the caller supplies.  The clause reads its rate factor
at `x · (Lg · eccentricityFoldFactor abar pEcc)` with a **law-free** constant.

the `constant_and_eccentricity_absorbed` premise performs the two absorptions; this
module wraps it for the `ℝ≥0∞`-valued conclusion, so that a real-valued class
split of the capstone's constant (module that module) is all the caller has to supply.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The hole's rate factor from the capstone's.**  A bound at the capstone's
length and constant, together with a class split of that constant, gives the
bound at the hole's length and at the law-free head. -/
theorem rateFactor_to_holeShape (abar : Mat d)
    {Hconst Claw Krest p p0 kappa epsilon x : ℝ} {A B : ℝ≥0∞}
    (hbound : A ≤ ENNReal.ofReal (Hconst *
        (epsilon * (x * eccentricityFoldFactor abar p0)) ^ kappa) * B)
    (hHle : Hconst ≤
      Claw * (max 1 (witnessEccentricity (symmPart abar))) ^ p * Krest)
    (hClaw : 0 ≤ Claw) (hkappa : 0 < kappa) (hp : 0 ≤ p) (hp0 : 0 ≤ p0)
    (heps : 0 ≤ epsilon) (hx : 0 ≤ x) :
    A ≤ ENNReal.ofReal (Claw *
        (epsilon * (x * (perGLengthFactor Krest kappa *
          eccentricityFoldFactor abar (p0 + p / kappa)))) ^ kappa) * B := by
  refine hbound.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hR0 : (0 : ℝ) ≤
      (epsilon * (x * eccentricityFoldFactor abar p0)) ^ kappa :=
    Real.rpow_nonneg
      (mul_nonneg heps (mul_nonneg hx (eccentricityFoldFactor_pos abar p0).le)) _
  calc Hconst * (epsilon * (x * eccentricityFoldFactor abar p0)) ^ kappa
      ≤ (Claw * (max 1 (witnessEccentricity (symmPart abar))) ^ p * Krest) *
          (epsilon * (x * eccentricityFoldFactor abar p0)) ^ kappa :=
        mul_le_mul_of_nonneg_right hHle hR0
    _ ≤ Claw * (epsilon * (x * (perGLengthFactor Krest kappa *
          eccentricityFoldFactor abar (p0 + p / kappa)))) ^ kappa :=
        constant_and_eccentricity_absorbed abar hClaw hkappa hp hp0 heps hx

end

end RowSupply
end HighContrast
end HCPolySupport
