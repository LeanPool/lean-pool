/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import LeanPool.HighContrastHomogenization.Provider.Regularity.EffectiveScalePowerAbsorption

/-!
# High-contrast homogenization: Provider.Regularity.PowerLossRandomScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Random effective scales for deterministic power-law losses

This module applies the route-independent power-loss enlargement pointwise to
a measurable random scale and records its exact threshold-event behavior.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Enlarge a random scale pointwise so a deterministic prefactor `A` is
absorbed into a negative power with exponent `kappa`. -/
@[expose]
noncomputable def powerLossRandomScale {Omega : Type*}
    (A kappa : ℝ) (X : Omega → ℝ) : Omega → ℝ :=
  fun omega => powerLossEffectiveScale A kappa (X omega)

/-- A prefactor at least one enlarges every nonnegative sample scale. -/
theorem le_powerLossRandomScale {Omega : Type*} {A kappa : ℝ}
    {X : Omega → ℝ} (hA : 1 ≤ A) (hkappa : 0 < kappa)
    {omega : Omega} (hX : 0 ≤ X omega) :
    X omega ≤ powerLossRandomScale A kappa X omega := by
  exact le_powerLossEffectiveScale hA hkappa hX

/-- A pointwise unit lower bound is inherited by the power-loss scale. -/
theorem one_le_powerLossRandomScale {Omega : Type*} {A kappa : ℝ}
    {X : Omega → ℝ} (hA : 1 ≤ A) (hkappa : 0 < kappa)
    {omega : Omega} (hX : 1 ≤ X omega) :
    1 ≤ powerLossRandomScale A kappa X omega := by
  exact hX.trans (le_powerLossRandomScale hA hkappa (zero_le_one.trans hX))

/-- The deterministic prefactor is absorbed exactly at every sample. -/
theorem prefactor_mul_rpow_ratio_eq_rpow_powerLossRandomScale
    {Omega : Type*} {A kappa r : ℝ} {X : Omega → ℝ} {omega : Omega}
    (hA : 0 < A) (hkappa : 0 < kappa)
    (hX : 0 < X omega) (hr : 0 < r) :
    A * (r / X omega) ^ (-kappa) =
      (r / powerLossRandomScale A kappa X omega) ^ (-kappa) := by
  exact prefactor_mul_rpow_ratio_eq_rpow_effectiveScale hA hkappa hX hr

end

end HighContrast
end HCPolySupport
