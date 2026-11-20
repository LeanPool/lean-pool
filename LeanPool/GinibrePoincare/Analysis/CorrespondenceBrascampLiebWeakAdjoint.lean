/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeakAdjoint.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakTests
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebDensityGenerator
/-!
# Correspondence Brascamp Lieb weak adjoint

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_weak_weighted_adjoint`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
/-- Actual ordinary distributional gradients satisfy the weighted adjoint
identity internally, including C² rather than analytic potentials. -/
theorem correspondenceBrascampLieb_weak_weighted_adjoint
    (W u G : E → ℝ) (v : E) (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : CorrespondenceBrascampLiebLocallyL2 G)
    (hw : CorrespondenceBrascampLiebHasWeakDerivative u G v)
    (θ : E → ℝ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ x, G x*θ x ∂correspondenceBrascampLiebMeasure W) =
      ∫ x, u x*(bakryEmeryGibbsDirectional W v x*θ x-
        bakryEmeryGibbsDirectional θ v x) ∂correspondenceBrascampLiebMeasure W := by
  let ρ := bakryEmeryGibbsWeight W
  have hρ : ContDiff ℝ 1 ρ := Real.contDiff_exp.comp hW.neg
  have he := correspondenceBrascampLieb_weak_test_C1 W u G v hW.continuous hu hG hw
    (ρ*θ) (hρ.mul hθ) hc.mul_left
  have hder (x : E) : fderiv ℝ (ρ*θ) x v =
      ρ x*(bakryEmeryGibbsDirectional θ v x-
        bakryEmeryGibbsDirectional W v x*θ x) := by
    rw [fderiv_mul (hρ.differentiable (by norm_num) x) (hθ.differentiable (by norm_num) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have hd := correspondenceBrascampLieb_density_derivative W hW v x
    change fderiv ℝ ρ x v = -bakryEmeryGibbsDirectional W v x*ρ x at hd
    rw [hd]
    unfold bakryEmeryGibbsDirectional
    ring
  rw [correspondenceBrascampLieb_integral_density W _ hW.continuous,
    correspondenceBrascampLieb_integral_density W _ hW.continuous]
  calc
    _ = ∫ x, (ρ*θ) x*G x := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => by simp only [Pi.mul_apply]; dsimp [ρ]; ring
    _ = -(∫ x, fderiv ℝ (ρ*θ) x v*u x) := he
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all volume fun x => by
        dsimp only
        rw [hder]
        dsimp [ρ]
        ring

end
end GinibrePoincare
