/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperOrdinaryBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedBlockProfile

/-!
# UpperSaturatedOrdinaryComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Comparing the saturated and polynomial ordinary profiles

The strict-descendant saturated amplitude used for `1 ≤ q ≤ 2` is
pointwise no larger than the polynomial ordinary amplitude used by the common
envelope route for `q ≥ 2`.  Thus one proved per-cube estimate at the
saturated scale can feed both deterministic aggregation mechanisms.

This file supplies only that algebraic comparison.  It proves no per-cube
analytic estimate, does not treat the depth-zero/root row, and does not combine
any random lanes.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

/-- The saturated strict-descendant scale is bounded by the polynomial
ordinary scale with the same head constant. -/
theorem upperSaturatedPerCubeAmplitude_le_upperOrdinary
    {C cstar gamma : ℝ} (hC : 0 ≤ C) (hcstar : 0 ≤ cstar⁻¹)
    (k : ℕ) :
    upperSaturatedPerCubeAmplitude C cstar gamma k ≤
      upperOrdinaryPerCubeAmplitude C cstar gamma k := by
  have hcoef : 0 ≤ C * cstar⁻¹ := mul_nonneg hC hcstar
  have hpow : 0 ≤ (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [upperSaturatedPerCubeAmplitude, upperOrdinaryPerCubeAmplitude]
  calc
    C * cstar⁻¹ * min 1 (gamma * ((k : ℝ) + 1)) *
          (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) ≤
        C * cstar⁻¹ * (gamma * ((k : ℝ) + 1)) *
          (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hcoef) hpow
    _ = C * cstar⁻¹ * gamma * ((k : ℝ) + 1) *
          (3 : ℝ) ^ (gamma * ((k : ℝ) + 1)) := by ring

/-- Consequently the joint spatial-and-depth price of the saturated row fits
the existing common-envelope polynomial profile.  This remains an algebraic
profile comparison, not a statement that an actual row has this amplitude. -/
theorem triadicJointDepthEntropyConst_mul_upperSaturatedPerCubeAmplitude_le_bound
    (d : ℕ) {C cstar gamma : ℝ} (hC : 0 ≤ C)
    (hcstar : 0 ≤ cstar⁻¹) (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (k : ℕ) :
    triadicJointDepthEntropyConst d * ((k : ℝ) + 1) *
        upperSaturatedPerCubeAmplitude C cstar gamma k ≤
      upperPolyProfile (upperOrdinaryJointProfileBound d C cstar gamma)
        gamma k := by
  have hrow := upperSaturatedPerCubeAmplitude_le_upperOrdinary
    (gamma := gamma) hC hcstar k
  have hfactor : 0 ≤ triadicJointDepthEntropyConst d * ((k : ℝ) + 1) :=
    mul_nonneg (triadicJointDepthEntropyConst_pos d).le (by positivity)
  exact (mul_le_mul_of_nonneg_left hrow hfactor).trans
    (triadicJointDepthEntropyConst_mul_upperOrdinaryPerCubeAmplitude_le_bound
      d hC hcstar hgamma hgamma1 k)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
