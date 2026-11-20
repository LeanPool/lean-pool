/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebGibbs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCompactEnergy
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-!
# Correspondence Brascamp Lieb Gibbs

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_integral_density`,
`correspondenceBrascampLieb_integrable_compact`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- The unnormalized Gibbs measure with density `bakryEmeryGibbsWeight W` with respect to
`volume`. -/
abbrev correspondenceBrascampLiebMeasure (W : E → ℝ) : Measure E :=
  correspondenceWeightedEllipticMeasure (bakryEmeryGibbsWeight W)

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_integral_density
    (W g : E → ℝ) (hW : Continuous W) :
    (∫ x, g x ∂correspondenceBrascampLiebMeasure W) =
      ∫ x, g x * bakryEmeryGibbsWeight W x := by
  unfold correspondenceBrascampLiebMeasure correspondenceWeightedEllipticMeasure
  have hw : Continuous (bakryEmeryGibbsWeight W) := Real.continuous_exp.comp hW.neg
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal
    (ae_of_all volume fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (show 0 ≤ bakryEmeryGibbsWeight W x from (Real.exp_pos _).le),
    smul_eq_mul]
  exact mul_comm _ _

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_integrable_compact
    (W g : E → ℝ) (hW : Continuous W) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable g (correspondenceBrascampLiebMeasure W) := by
  apply (correspondenceWeightedElliptic_integrable_density
    (bakryEmeryGibbsWeight W) g (Real.continuous_exp.comp hW.neg)
    (fun _ => Real.exp_pos _)).mpr
  exact ((Real.continuous_exp.comp hW.neg).mul hg).integrable_of_hasCompactSupport hc.mul_left

end
end GinibrePoincare
