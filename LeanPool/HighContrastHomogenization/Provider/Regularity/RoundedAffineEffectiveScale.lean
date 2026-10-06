/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffinePairing
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedWeakSolutionPullback

/-!
# High-contrast homogenization: Provider.Regularity.RoundedAffineEffectiveScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The affine effective-scale multiplier

This module records the affine amplitude and places its sharp
positive-power absorption factor into one deterministic effective scale.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- The sharp rounded-affine amplitude:
`C_aff(d) * overlinePi^(1/2)`. -/
@[expose]
noncomputable def roundedAffineLossAmplitude
    (Caff overlinePi : ℝ) : ℝ :=
  Caff * Real.sqrt overlinePi

/-- The affine scale multiplier
`max {1, (C_aff(d) * overlinePi^(1/2))^(1/kappaCube)}`. -/
@[expose]
noncomputable def roundedAffineMultiplier
    (Caff overlinePi kappaCube : ℝ) : ℝ :=
  max 1 ((roundedAffineLossAmplitude Caff overlinePi) ^ kappaCube⁻¹)

/-- Insert the affine loss once into a pre-existing common scale. -/
@[expose]
noncomputable def roundedAffineEffectiveScale
    (Caff overlinePi kappaCube : ℝ) (X : ℝ) : ℝ :=
  roundedAffineMultiplier Caff overlinePi kappaCube * X

theorem one_le_roundedAffineMultiplier
    (Caff overlinePi kappaCube : ℝ) :
    1 ≤ roundedAffineMultiplier Caff overlinePi kappaCube :=
  le_max_left _ _

theorem roundedAffineMultiplier_pos
    (Caff overlinePi kappaCube : ℝ) :
    0 < roundedAffineMultiplier Caff overlinePi kappaCube :=
  zero_lt_one.trans_le
    (one_le_roundedAffineMultiplier Caff overlinePi kappaCube)

/-- The multiplier has enough `kappaCube`-power to absorb the full
rounded-affine amplitude. -/
theorem roundedAffineLossAmplitude_le_multiplier_rpow
    {Caff overlinePi kappaCube : ℝ}
    (hCaff : 0 < Caff) (hPi : 0 < overlinePi)
    (hkappa : 0 < kappaCube) :
    roundedAffineLossAmplitude Caff overlinePi ≤
      (roundedAffineMultiplier Caff overlinePi kappaCube) ^ kappaCube := by
  have hA : 0 < roundedAffineLossAmplitude Caff overlinePi :=
    mul_pos hCaff (Real.sqrt_pos.2 hPi)
  have hrootNonneg : 0 ≤
      (roundedAffineLossAmplitude Caff overlinePi) ^ kappaCube⁻¹ :=
    Real.rpow_nonneg hA.le _
  have hmultPos : 0 < roundedAffineMultiplier Caff overlinePi kappaCube :=
    roundedAffineMultiplier_pos Caff overlinePi kappaCube
  have hpowers := (Real.rpow_le_rpow_iff hrootNonneg hmultPos.le hkappa).mpr
    (le_max_right (1 : ℝ)
      ((roundedAffineLossAmplitude Caff overlinePi) ^ kappaCube⁻¹))
  rwa [Real.rpow_inv_rpow hA.le hkappa.ne'] at hpowers

/-- The affine enlargement never decreases a nonnegative source scale. -/
theorem le_roundedAffineEffectiveScale
    (Caff overlinePi kappaCube X : ℝ) (hX : 0 ≤ X) :
    X ≤ roundedAffineEffectiveScale Caff overlinePi kappaCube X := by
  unfold roundedAffineEffectiveScale
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (one_le_roundedAffineMultiplier Caff overlinePi kappaCube) hX

/-- A unit-lower-bounded source scale remains unit-lower-bounded after the
single affine enlargement. -/
theorem one_le_roundedAffineEffectiveScale
    (Caff overlinePi kappaCube X : ℝ) (hX : 1 ≤ X) :
    1 ≤ roundedAffineEffectiveScale Caff overlinePi kappaCube X :=
  le_trans hX (le_roundedAffineEffectiveScale Caff overlinePi kappaCube X
    (zero_le_one.trans hX))

/-- Applying the fixed affine multiplier preserves measurability of a random
source scale. -/
theorem Measurable.roundedAffineEffectiveScale {Omega : Type*}
    [MeasurableSpace Omega] (Caff overlinePi kappaCube : ℝ)
    {X : Omega → ℝ} (hX : Measurable X) :
    Measurable (fun ω ↦
      roundedAffineEffectiveScale Caff overlinePi kappaCube (X ω)) := by
  exact hX.const_mul _

end

end HighContrast
end HCPolySupport
