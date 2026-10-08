/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeFamilyTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.AffineRateAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem multiplier_rpow_mul_ratio_eq
    {mult kappa x r : ℝ} (hmult : 0 < mult)
    (hx : 0 < x) (hr : 0 < r) :
    mult ^ kappa * (r / x) ^ (-kappa) =
      (r / (mult * x)) ^ (-kappa) := by
  have hratio : r / (mult * x) = (r / x) / mult := by
    field_simp [hmult.ne', hx.ne']
  rw [hratio, Real.div_rpow (div_nonneg hr.le hx.le) hmult.le,
    Real.rpow_neg hmult.le, div_inv_eq_mul, mul_comm]

/-- The affine negative-one loss is paid exactly by the multiplier retained
between the targeted certificate scale and the common root scale. -/
theorem affineRate_absorption
    {d : ℕ} [NeZero d] {S : Mat d} (hS : S.PosDef)
    {kappa x r : ℝ} (hKappa : 0 < kappa)
    (hx : 0 < x) (hr : 0 < r) {m : ℤ}
    (hrm : r ≤ (3 : ℝ) ^ m) :
    Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) *
          ((((3 : ℝ) ^ m) / x) ^ (-kappa)) ≤
      (Real.sqrt d / Transport.roundedOuterResponseAffineConstant d) *
        (r /
          (roundedAffineMultiplier
              (Transport.roundedOuterResponseAffineConstant d)
              (specBound S * specBound S⁻¹) kappa * x)) ^ (-kappa) := by
  let Caff : ℝ := Transport.roundedOuterResponseAffineConstant d
  let overlinePi : ℝ := specBound S * specBound S⁻¹
  let mult : ℝ := roundedAffineMultiplier Caff overlinePi kappa
  let rateM : ℝ := ((((3 : ℝ) ^ m) / x) ^ (-kappa))
  let rateR : ℝ := (r / x) ^ (-kappa)
  have hCaff : 0 < Caff := by
    simpa only [Caff] using Transport.roundedOuterResponseAffineConstant_pos d
  have hPi : 0 < overlinePi := by
    have hecc := Transport.zero_lt_witnessEccentricity hS
    simpa only [overlinePi, witnessEccentricity, Real.sqrt_pos] using hecc
  have hmult : 0 < mult := by
    simpa only [mult] using roundedAffineMultiplier_pos Caff overlinePi kappa
  have hrateM : 0 ≤ rateM := by
    dsimp only [rateM]
    exact Real.rpow_nonneg (by positivity) _
  have hrateR : 0 ≤ rateR := by
    dsimp only [rateR]
    exact Real.rpow_nonneg (by positivity) _
  have hratio : r / x ≤ ((3 : ℝ) ^ m) / x :=
    div_le_div_of_nonneg_right hrm hx.le
  have hrateMono : rateM ≤ rateR := by
    dsimp only [rateM, rateR]
    exact Real.rpow_le_rpow_of_nonpos (div_pos hr hx) hratio
      (by linarith only [hKappa])
  have hloss : Caff * witnessEccentricity S ≤ mult ^ kappa := by
    have hraw := roundedAffineLossAmplitude_le_multiplier_rpow
      hCaff hPi hKappa
    simpa only [roundedAffineLossAmplitude, Caff, overlinePi,
      witnessEccentricity, mult] using hraw
  have habsorb : mult ^ kappa * rateR =
      (r / (mult * x)) ^ (-kappa) := by
    simpa only [rateR] using
      multiplier_rpow_mul_ratio_eq hmult hx hr
  have hfactor := sqrt_H1AffineFactor_normalizedRoot_le hS
  calc
    Real.sqrt (h1AffineFactor (Selection.normalizedRoot S)) * rateM ≤
        (Real.sqrt d * witnessEccentricity S) * rateM :=
      mul_le_mul_of_nonneg_right hfactor hrateM
    _ = (Real.sqrt d / Caff) *
        ((Caff * witnessEccentricity S) * rateM) := by
      field_simp [hCaff.ne']
    _ ≤ (Real.sqrt d / Caff) * ((mult ^ kappa) * rateR) := by
      have hinner : (Caff * witnessEccentricity S) * rateM ≤
          (mult ^ kappa) * rateR :=
        calc
          (Caff * witnessEccentricity S) * rateM ≤
              (mult ^ kappa) * rateM :=
            mul_le_mul_of_nonneg_right hloss hrateM
          _ ≤ (mult ^ kappa) * rateR :=
            mul_le_mul_of_nonneg_left hrateMono
              (Real.rpow_nonneg hmult.le _)
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (Real.sqrt d / Caff) *
        (r / (mult * x)) ^ (-kappa) := by rw [habsorb]
    _ = _ := by simp only [Caff, mult, overlinePi]

end

end HighContrast
end HCPolySupport
