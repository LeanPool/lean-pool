/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.SmallWaves

/-!
# G1RatioTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Sign facts for the Appendix-D threshold of the `𝒢₁` lane

ABK26, §4.1, `l.ratio.of.good.scales.for.k`, Step 3, splits a `θ`-density of
`𝒢₁`-bad scales into a `θ/2`-density for one of the two lanes `eventG1a`,
`eventG1b`.  What this module keeps are the two sign facts that step consumes:

* `half_le_one_sub_gamma` — the standing assumption `γ ≤ 1/4` of
  `ShellLawPrefix` makes the large-waves Appendix-D weight rate `s' = 1/2`
  admissible;
* `appendixD_level_nonneg` — the Appendix-D threshold level is nonnegative, the
  `hlam` slot of both lanes' reductions.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 3.
* ABK26, `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Sign facts for the Appendix-D threshold -/

/-- The standing assumption `γ ≤ 1/4` of `ShellLawPrefix` makes the large-waves
Appendix-D weight rate `s' = 1/2` admissible: `1/2 ≤ 1 - γ`. -/
theorem half_le_one_sub_gamma (M : ABKModel d) : (1 : ℝ) / 2 ≤ 1 - M.gamma := by
  have h := M.shellPrefix.gamma_le_quarter
  linarith only [h]


/-- The Appendix-D threshold level is nonnegative — the `hlam` slot of both
lanes' reductions. -/
theorem appendixD_level_nonneg {sprime p theta : ℝ} (hs : 0 < sprime)
    (htheta : 0 < theta) :
    0 ≤ 9 * sprime⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) := by
  have h1 : (0 : ℝ) ≤ 9 * sprime⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ Cstar ^ (1 / p) := Real.rpow_nonneg Cstar_pos.le _
  have h3 : (0 : ℝ) ≤ theta ^ (-1 / p) := Real.rpow_nonneg htheta.le _
  exact mul_nonneg (mul_nonneg h1 h2) h3

end

end Algsuperdiff.Section4.Provider.Proportion
