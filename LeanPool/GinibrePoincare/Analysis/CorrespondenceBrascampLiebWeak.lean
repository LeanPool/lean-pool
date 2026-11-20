/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeak.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakDual
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebDense
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebLipschitz
/-!
# Correspondence Brascamp Lieb weak

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_localLipschitz_probability_variance`,
`correspondenceBrascampLieb_weak_probability_variance`.
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
/-- Real Brascamp–Lieb on actual ordinary distributional Sobolev domains.
Only the value is globally L²; the physical gradient is locally L² and
has finite inverse-Hessian energy. No global ordinary gradient L² bound
or uniform curvature lower bound is imposed. -/
theorem correspondenceBrascampLieb_weak_variance
    (W u : E → ℝ) (G : E → ι → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hE : Integrable (correspondenceBrascampLiebWeakInverseEnergy W G b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W u x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x
      ∂correspondenceBrascampLiebMeasure W := by
  let := correspondenceBrascampLieb_finite_measure W hWi
  let v := (correspondenceBrascampLieb_center_memLp W u hu).toLp
    (correspondenceBrascampLiebCenter W u)
  have hv : v ∈ (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure := by
    rw [correspondenceBrascampLieb_core_dense_centered W b hW]
    exact correspondenceBrascampLieb_center_orthogonal W u hWi hu
  rw [← correspondenceBrascampLieb_toLp_norm_sq _ _
    (correspondenceBrascampLieb_center_memLp W u hu)]
  apply correspondenceBrascampLieb_duality v (correspondenceBrascampLiebCoreRange W b hW)
    (∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x ∂correspondenceBrascampLiebMeasure W)
  · apply integral_nonneg
    intro x
    change 0 ≤ G x ⬝ᵥ (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ G x
    simpa only [star_trivial] using (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg (G x)
  · exact hv
  · rintro _ ⟨f, rfl⟩
    exact correspondenceBrascampLieb_weak_centered_core_bound W u G b hW hu hG hw hpos hE f

omit [CompleteSpace E] in
/-- The classical locally Lipschitz domain, with all actual distributional
and local gradient integrability inputs discharged internally by
Rademacher, Lipschitz extension, and genuine integration by parts. -/
theorem correspondenceBrascampLieb_localLipschitz_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : LocallyLipschitz g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, correspondenceBrascampLiebCenter W g x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  exact correspondenceBrascampLieb_weak_variance W g (correspondenceBrascampLiebGradient g b) b
    hW hWi hpos hgL2
    (fun i => correspondenceBrascampLieb_localLipschitz_localL2 g hg (b i))
    (fun i => correspondenceBrascampLieb_localLipschitz_weak_derivative g hg (b i)) hgE

omit [CompleteSpace E] in
/-- Probability-normalized classical locally Lipschitz Brascamp–Lieb. -/
theorem correspondenceBrascampLieb_localLipschitz_probability_variance
    (W g : E → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hMass : (∫ x, bakryEmeryGibbsWeight W x) = 1)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hg : LocallyLipschitz g) (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, (g x-(∫ y, g y ∂correspondenceBrascampLiebMeasure W))^2
      ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  simpa only [correspondenceBrascampLiebCenter, correspondenceBrascampLiebMean, hMass, div_one]
      using
    correspondenceBrascampLieb_localLipschitz_variance W g b hW hWi hpos hg hgL2 hgE

omit [CompleteSpace E] in
/-- Probability-normalized ordinary weak-domain Brascamp–Lieb. -/
theorem correspondenceBrascampLieb_weak_probability_variance
    (W u : E → ℝ) (G : E → ι → ℝ) (b : OrthonormalBasis ι ℝ E)
    (hW : ContDiff ℝ 2 W) (hWi : Integrable (bakryEmeryGibbsWeight W))
    (hMass : (∫ x, bakryEmeryGibbsWeight W x) = 1)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hE : Integrable (correspondenceBrascampLiebWeakInverseEnergy W G b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, (u x-(∫ y, u y ∂correspondenceBrascampLiebMeasure W))^2
      ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x
      ∂correspondenceBrascampLiebMeasure W := by
  simpa only [correspondenceBrascampLiebCenter, correspondenceBrascampLiebMean, hMass, div_one]
      using
    correspondenceBrascampLieb_weak_variance W u G b hW hWi hpos hu hG hw hE

end
end GinibrePoincare
