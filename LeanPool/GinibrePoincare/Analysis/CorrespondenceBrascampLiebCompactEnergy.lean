/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCompactEnergy.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebHessian
public import Mathlib.Topology.Instances.Matrix
/-!
# Correspondence Brascamp Lieb compact energy

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_inverse_energy_integrable`.
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

/-- The inverse-Hessian energy `∇g ⬝ᵥ (∇²W)⁻¹ *ᵥ ∇g` at `x`, with gradient and Hessian taken in
the directions `b`. -/
def correspondenceBrascampLiebInverseEnergy (W g : E → ℝ) (b : ι → E) (x : E) : ℝ :=
  correspondenceBrascampLiebGradient g b x ⬝ᵥ
    (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ correspondenceBrascampLiebGradient g b x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [DecidableEq ι] [Fintype ι] in
theorem correspondenceBrascampLieb_hessian_continuous
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W) :
    Continuous (correspondenceBrascampLiebHessian W b) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)).fderiv_right
    (m := 0) (by norm_num)).continuous.clm_apply continuous_const

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_hessian_inverse_continuous
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Continuous (fun x => (correspondenceBrascampLiebHessian W b x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd : (correspondenceBrascampLiebHessian W b x).det ≠ 0 :=
    ((correspondenceBrascampLiebHessian W b x).isUnit_iff_isUnit_det.mp (hpos x).isUnit).ne_zero
  have hi : ContinuousAt Ring.inverse (correspondenceBrascampLiebHessian W b x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  exact (continuousAt_matrix_inv _ hi).comp
    (correspondenceBrascampLieb_hessian_continuous W b hW).continuousAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_inverse_energy_continuous
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Continuous (correspondenceBrascampLiebInverseEnergy W g b) := by
  have hG : Continuous (correspondenceBrascampLiebGradient g b) := by
    apply continuous_pi
    intro i
    exact (hg.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hI := correspondenceBrascampLieb_hessian_inverse_continuous W b hW hpos
  unfold correspondenceBrascampLiebInverseEnergy
  exact hG.dotProduct (hI.matrix_mulVec hG)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_inverse_energy_compact
    (W g : E → ℝ) (b : ι → E) (hc : HasCompactSupport g) :
    HasCompactSupport (correspondenceBrascampLiebInverseEnergy W g b) := by
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  apply hx
  have hG : correspondenceBrascampLiebGradient g b x = 0 := by
    funext i
    simp [correspondenceBrascampLiebGradient, bakryEmeryGibbsDirectional, hz]
  simp [correspondenceBrascampLiebInverseEnergy, hG]

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_inverse_energy_integrable
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef) :
    Integrable (fun x => correspondenceBrascampLiebInverseEnergy W g b x *
      bakryEmeryGibbsWeight W x) := by
  exact ((correspondenceBrascampLieb_inverse_energy_continuous W g b hW hg hpos).mul
    (Real.continuous_exp.comp hW.continuous.neg)).integrable_of_hasCompactSupport
      ((correspondenceBrascampLieb_inverse_energy_compact W g b hc).mul_right)

end
end GinibrePoincare
