/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp

/-!
# High-contrast homogenization: Provider.Regularity.EffectiveScalePowerAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Effective-scale absorption of a power-law prefactor

This module isolates the route-independent real algebra for absorbing a
positive multiplicative loss into the reference scale of a negative power.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- The scale enlargement that absorbs a prefactor `A` from a decay rate with
positive exponent `kappa`. -/
@[expose]
noncomputable def powerLossEffectiveScale (A kappa x : ℝ) : ℝ :=
  A ^ kappa⁻¹ * x

/-- A prefactor at least one only enlarges a nonnegative base scale. -/
theorem le_powerLossEffectiveScale {A kappa x : ℝ}
    (hA : 1 ≤ A) (hkappa : 0 < kappa) (hx : 0 ≤ x) :
    x ≤ powerLossEffectiveScale A kappa x := by
  unfold powerLossEffectiveScale
  have hfactor : 1 ≤ A ^ kappa⁻¹ :=
    Real.one_le_rpow hA (inv_nonneg.mpr hkappa.le)
  calc
    x = 1 * x := (one_mul x).symm
    _ ≤ A ^ kappa⁻¹ * x := mul_le_mul_of_nonneg_right hfactor hx

/-- Absorbing `A` into the effective scale is an exact identity for a negative
power-law profile. -/
theorem prefactor_mul_rpow_ratio_eq_rpow_effectiveScale
    {A kappa x r : ℝ} (hA : 0 < A) (hkappa : 0 < kappa)
    (hx : 0 < x) (hr : 0 < r) :
    A * (r / x) ^ (-kappa) =
      (r / powerLossEffectiveScale A kappa x) ^ (-kappa) := by
  let B : ℝ := A ^ kappa⁻¹
  have hB : 0 < B := Real.rpow_pos_of_pos hA kappa⁻¹
  have hBpow : B ^ kappa = A := by
    dsimp only [B]
    exact Real.rpow_inv_rpow hA.le hkappa.ne'
  have hratio : r / (B * x) = (r / x) / B := by
    field_simp [hx.ne', hB.ne']
  rw [powerLossEffectiveScale, show A ^ kappa⁻¹ = B from rfl, hratio,
    Real.div_rpow (div_nonneg hr.le hx.le) hB.le,
    Real.rpow_neg hB.le, hBpow, div_inv_eq_mul, mul_comm]

end

end HighContrast
end HCPolySupport
