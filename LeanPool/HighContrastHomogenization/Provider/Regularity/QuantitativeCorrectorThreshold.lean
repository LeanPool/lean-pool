/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.QuantitativeEffectiveScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointGoodTailEquation

/-!
# High-contrast homogenization: Provider.Regularity.QuantitativeCorrectorThreshold

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A quantitative certificate at the local-corrector threshold

The small target amplitude is selected before coefficient samples.  One common
effective scale then places every quantitative certificate strictly below the
joint-local-corrector threshold.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Pointwise amplitude which makes the resulting summable-tail tolerance
exactly `c / 2`. -/
@[expose]
noncomputable def correctorTargetAmplitude (c kappa : ℝ) : ℝ :=
  (c / 2) * (1 - (3 : ℝ) ^ (-kappa))

theorem correctorTargetAmplitude_pos {c kappa : ℝ}
    (hc : 0 < c) (hKappa : 0 < kappa) :
    0 < correctorTargetAmplitude c kappa := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hKappa)
  exact mul_pos (by positivity) (sub_pos.mpr hpow)

theorem correctorTargetAmplitude_div {c kappa : ℝ}
    (hKappa : 0 < kappa) :
    correctorTargetAmplitude c kappa /
        (1 - (3 : ℝ) ^ (-kappa)) = c / 2 := by
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hKappa)
  unfold correctorTargetAmplitude
  exact mul_div_cancel_right₀ (c / 2) (sub_ne_zero.mpr hpow.ne.symm)

end

end HighContrast
end HCPolySupport
