/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebMass.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebGibbs
/-!
# Correspondence Brascamp Lieb mass

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_probability_measure`.
-/

@[expose] public section
open MeasureTheory Measure
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_mass
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    correspondenceBrascampLiebMeasure W Set.univ =
      ENNReal.ofReal (∫ x, bakryEmeryGibbsWeight W x) := by
  unfold correspondenceBrascampLiebMeasure correspondenceWeightedEllipticMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all volume fun x => (Real.exp_pos _).le)).symm

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_finite_measure
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    IsFiniteMeasure (correspondenceBrascampLiebMeasure W) := by
  refine ⟨?_⟩
  rw [correspondenceBrascampLieb_mass W hi]
  exact ENNReal.ofReal_lt_top

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_positive_mass
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W)) :
    0 < ∫ x, bakryEmeryGibbsWeight W x := by
  exact integral_exp_pos hi

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_probability_measure
    (W : E → ℝ) (hi : Integrable (bakryEmeryGibbsWeight W))
    (hm : (∫ x, bakryEmeryGibbsWeight W x) = 1) :
    IsProbabilityMeasure (correspondenceBrascampLiebMeasure W) := by
  refine ⟨?_⟩
  rw [correspondenceBrascampLieb_mass W hi, hm]
  norm_num

end
end GinibrePoincare
