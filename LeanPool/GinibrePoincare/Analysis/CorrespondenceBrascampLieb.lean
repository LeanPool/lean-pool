/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLieb.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebDense
/-!
# Correspondence Brascamp Lieb

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_probability_variance`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace E] in
/-- The concrete real Brascamp–Lieb inequality with the variable inverse
Hessian, for arbitrary C² strictly convex integrable Gibbs potentials.
There is no uniform lower curvature assumption or elliptic certificate. -/
theorem correspondenceBrascampLieb_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  let := correspondenceBrascampLieb_finite_measure W hWi
  have hgc : ContDiff ℝ 1 (correspondenceBrascampLiebCenter W g) := hg.sub contDiff_const
  have hgcL2 := correspondenceBrascampLieb_center_memLp W g hgL2
  have he : correspondenceBrascampLiebInverseEnergy W (correspondenceBrascampLiebCenter W g) b =
      correspondenceBrascampLiebInverseEnergy W g b := by
    funext x
    unfold correspondenceBrascampLiebInverseEnergy
    rw [correspondenceBrascampLieb_center_gradient W g b]
  have hgcE : Integrable (correspondenceBrascampLiebInverseEnergy W
      (correspondenceBrascampLiebCenter W g) b) (correspondenceBrascampLiebMeasure W) := by
    rw [he]
    exact hgE
  have hc : hgcL2.toLp (correspondenceBrascampLiebCenter W g) ∈
      (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure := by
    rw [correspondenceBrascampLieb_core_dense_centered W b hW]
    exact correspondenceBrascampLieb_center_orthogonal W g hWi hgL2
  have hv := correspondenceBrascampLieb_closed_core_bound W (correspondenceBrascampLiebCenter W g)
    b hW hgc hpos hgcL2 hgcE hc
  rwa [he] at hv

omit [CompleteSpace E] in
/-- Probability-normalized form of the exact inverse-Hessian inequality. -/
theorem correspondenceBrascampLieb_probability_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hMass : (∫ x, bakryEmeryGibbsWeight W x) = 1)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : ContDiff ℝ 1 g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, (g x-(∫ y, g y ∂correspondenceBrascampLiebMeasure W))^2
      ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  simpa only [correspondenceBrascampLiebCenter, correspondenceBrascampLiebMean, hMass, div_one]
      using
    correspondenceBrascampLieb_variance W g b hW hWi hpos hg hgL2 hgE

end
end GinibrePoincare
