/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderNormalizedReferencePowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledObservationComparisonPricing
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.MidpointResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ObservationHomogenizationErrorPowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ResidualScaledCoeffTransport
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.PrintDirectResponseWindowComposition
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.RowRetainingGoodScaleInterface

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row-retaining root certificate interface

The normalized-reference certificate used by deterministic consumers is a
lossy projection of the stochastic row which produced it.  The response-rate
consumer retains that row together with the projected good-scale certificate.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Root good-scale data with the producing physical block row retained.
The row rate is twice the response rate because the response converter takes
a square root. -/
structure RowRetainingPrintOrderGoodScale
    (d : ℕ) [NeZero d] (g c kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) where
  good : PrintOrderRateBearingCommonAffineGoodScale
    d g c kappaRate abar a x
  delta : ℝ
  sourceScale : CoeffSpace d → ℝ
  activationScale : CoeffSpace d → ℝ
  delta_nonneg : 0 ≤ delta
  activation_one : 1 ≤ activationScale a
  source_le_activation : sourceScale a ≤ activationScale a
  activation_le_common : activationScale a ≤ x
  row : Quenched.HasAllLaterPhysicalBlockRow
    (Certificate.printRowOrder g) (2 * kappaRate) delta
      (Book.Ch02.constantBlockMatrix abar) sourceScale activationScale a

/-- The transported row amplitude contains the requested physical-frame
power before any response aggregation is performed. -/
theorem sqrt_triadicallyScaledRowAmplitude_le_physicalFrameRate
    {delta activation epsilon x kappa : ℝ} {N : ℕ}
    (hdelta : 0 ≤ delta) (hactivation : 0 ≤ activation)
    (hepsilon : 0 < epsilon) (hkappa : 0 ≤ kappa)
    (hax : activation ≤ x)
    (hN : epsilon⁻¹ ≤ (3 : ℝ) ^ N) :
    Real.sqrt (triadicallyScaledRowAmplitude delta activation N (2 * kappa)) ≤
      Real.sqrt delta * (epsilon * x) ^ kappa := by
  have hthree : 0 < (3 : ℝ) ^ N := by positivity
  have hratio : activation / (3 : ℝ) ^ N ≤ epsilon * x := by
    have hinv : ((3 : ℝ) ^ N)⁻¹ ≤ epsilon := by
      apply (inv_le_iff_one_le_mul₀ hthree).2
      have hepsinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
      calc
        1 ≤ epsilon * epsilon⁻¹ := by
          rw [mul_inv_cancel₀ hepsilon.ne']
        _ ≤ epsilon * (3 : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left hN hepsilon.le
    calc
      activation / (3 : ℝ) ^ N =
          ((3 : ℝ) ^ N)⁻¹ * activation := by
        rw [div_eq_inv_mul]
      _ ≤ epsilon * activation :=
        mul_le_mul_of_nonneg_right hinv hactivation
      _ ≤ epsilon * x :=
        mul_le_mul_of_nonneg_left hax hepsilon.le
  have hbase : 0 ≤ epsilon * x := by
    exact mul_nonneg hepsilon.le (hactivation.trans hax)
  have hpow :
      (activation / (3 : ℝ) ^ N) ^ (2 * kappa) ≤
        (epsilon * x) ^ (2 * kappa) :=
    Real.rpow_le_rpow (by positivity) hratio (mul_nonneg (by norm_num) hkappa)
  have hsqrtMono :
      Real.sqrt
          (delta * (activation / (3 : ℝ) ^ N) ^ (2 * kappa)) ≤
        Real.sqrt (delta * (epsilon * x) ^ (2 * kappa)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpow hdelta)
  calc
    Real.sqrt (triadicallyScaledRowAmplitude delta activation N (2 * kappa)) ≤
        Real.sqrt (delta * (epsilon * x) ^ (2 * kappa)) := by
      simpa only [triadicallyScaledRowAmplitude] using hsqrtMono
    _ = Real.sqrt delta * (epsilon * x) ^ kappa := by
      rw [Real.sqrt_mul hdelta]
      have hpowNonneg : 0 ≤ (epsilon * x) ^ kappa :=
        Real.rpow_nonneg hbase _
      rw [show (epsilon * x) ^ (2 * kappa) =
          ((epsilon * x) ^ kappa) ^ 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
        congr 1
        ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hpowNonneg]

end

end RowSupply
end HighContrast
end HCPolySupport
