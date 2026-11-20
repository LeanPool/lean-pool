/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCenter.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebConstants
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebMass
/-!
# Correspondence Brascamp Lieb center

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- The mean of `g` under the normalized Gibbs measure:
`∫ g ∂(correspondenceBrascampLiebMeasure W) / ∫ bakryEmeryGibbsWeight W`. -/
def correspondenceBrascampLiebMean (W g : E → ℝ) : ℝ :=
  (∫ x, g x ∂correspondenceBrascampLiebMeasure W) / (∫ x, bakryEmeryGibbsWeight W x)

/-- The centered function `g - correspondenceBrascampLiebMean W g`. -/
def correspondenceBrascampLiebCenter (W g : E → ℝ) (x : E) : ℝ :=
  g x - correspondenceBrascampLiebMean W g

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_center_memLp
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    MemLp (correspondenceBrascampLiebCenter W g) 2 (correspondenceBrascampLiebMeasure W) :=
  hg.sub (memLp_const (correspondenceBrascampLiebMean W g))

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_center_integral
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hi : Integrable (bakryEmeryGibbsWeight W))
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x ∂correspondenceBrascampLiebMeasure W) = 0 := by
  have hig : Integrable g (correspondenceBrascampLiebMeasure W) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  have hm : (correspondenceBrascampLiebMeasure W).real Set.univ =
      ∫ x, bakryEmeryGibbsWeight W x := by
    rw [Measure.real, correspondenceBrascampLieb_mass W hi,
      ENNReal.toReal_ofReal (correspondenceBrascampLieb_positive_mass W hi).le]
  unfold correspondenceBrascampLiebCenter
  rw [integral_sub hig (integrable_const _), integral_const, hm]
  simp only [smul_eq_mul, correspondenceBrascampLiebMean]
  field_simp [(correspondenceBrascampLieb_positive_mass W hi).ne']
  ring

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_center_orthogonal
    (W g : E → ℝ) [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hi : Integrable (bakryEmeryGibbsWeight W))
    (hg : MemLp g 2 (correspondenceBrascampLiebMeasure W)) :
    (correspondenceBrascampLieb_center_memLp W g hg).toLp
      (correspondenceBrascampLiebCenter W g) ∈ (ℝ ∙ correspondenceBrascampLiebOneL2 W)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  unfold correspondenceBrascampLiebOneL2
  rw [correspondenceBrascampLieb_toLp_inner]
  simp only [mul_one]
  exact correspondenceBrascampLieb_center_integral W g hi hg

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_center_gradient
    {ι : Type*} [Finite ι] (W g : E → ℝ) (b : ι → E) :
    correspondenceBrascampLiebGradient (correspondenceBrascampLiebCenter W g) b =
      correspondenceBrascampLiebGradient g b := by
  have := Fintype.ofFinite ι
  funext x i
  unfold correspondenceBrascampLiebGradient bakryEmeryGibbsDirectional
    correspondenceBrascampLiebCenter
  rw [fderiv_sub_const]

end
end GinibrePoincare
