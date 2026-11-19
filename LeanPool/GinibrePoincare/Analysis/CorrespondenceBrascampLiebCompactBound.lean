/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCompactBound.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebIntegralCS
/-!
# Correspondence Brascamp Lieb compact bound

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_compact_generator_bound`.
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

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [DecidableEq ι] [Fintype ι] in
theorem correspondenceBrascampLieb_gradient_continuous (g : E → ℝ) (b : ι → E)
    (hg : ContDiff ℝ 1 g) : Continuous (correspondenceBrascampLiebGradient g b) := by
  classical
  apply continuous_pi
  intro i
  exact (hg.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const

omit [DecidableEq ι] in
omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_gradient_quadratic_integrable
    (W f : E → ℝ) (b : ι → E) (M : E → Matrix ι ι ℝ)
    (hW : Continuous W) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hM : Continuous M) : Integrable (fun x =>
      correspondenceBrascampLiebGradient f b x ⬝ᵥ M x *ᵥ correspondenceBrascampLiebGradient f b x)
      (correspondenceBrascampLiebMeasure W) := by
  classical
  have hG := correspondenceBrascampLieb_gradient_continuous f b hf
  apply correspondenceBrascampLieb_integrable_compact W _ hW
    (hG.dotProduct (hM.matrix_mulVec hG))
  apply (hc.fderiv ℝ).mono
  intro x hx hz
  apply hx
  have he : correspondenceBrascampLiebGradient f b x = 0 := by
    funext i
    simp [correspondenceBrascampLiebGradient, bakryEmeryGibbsDirectional, hz]
  simp [he]

omit [CompleteSpace E] in
/-- The actual compact-generator dual bound. Finite inverse-Hessian energy
is the test-function hypothesis; all core integration facts are internal. -/
theorem correspondenceBrascampLieb_compact_generator_bound
    (W g f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W)) :
    (∫ x, g x * bakryEmeryGibbsGenerator W b f x
      ∂correspondenceBrascampLiebMeasure W)^2 ≤
    (∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W) *
    (∫ x, bakryEmeryGibbsGenerator W b f x^2 ∂correspondenceBrascampLiebMeasure W) := by
  let μ := correspondenceBrascampLiebMeasure W
  let G := correspondenceBrascampLiebGradient g b
  let F := correspondenceBrascampLiebGradient f b
  let H := correspondenceBrascampLiebHessian W b
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hG := correspondenceBrascampLieb_gradient_continuous g b hg
  have hF := correspondenceBrascampLieb_gradient_continuous f b hf1
  have hH := correspondenceBrascampLieb_hessian_continuous W b hW
  have hiF : Integrable (fun x => F x ⬝ᵥ H x *ᵥ F x) μ :=
    correspondenceBrascampLieb_gradient_quadratic_integrable W f b H
      hW.continuous hf1 hc hH
  have hiGF : Integrable (fun x => G x ⬝ᵥ F x) μ := by
    apply correspondenceBrascampLieb_integrable_compact W _ hW.continuous (hG.dotProduct hF)
    apply (hc.fderiv ℝ).mono
    intro x hx hz
    apply hx
    have he : F x = 0 := by
      funext i
      simp [F, correspondenceBrascampLiebGradient, bakryEmeryGibbsDirectional, hz]
    change G x ⬝ᵥ F x = 0
    rw [he]
    simp
  have hCS := correspondenceBrascampLieb_integral_inverse_hessian μ H G F hpos hgE hiF hiGF
  have hDir : (∫ x, g x * bakryEmeryGibbsGenerator W b f x ∂μ) =
      -(∫ x, G x ⬝ᵥ F x ∂μ) := by
    rw [correspondenceBrascampLieb_integral_density W _ hW.continuous,
      correspondenceBrascampLieb_integral_density W _ hW.continuous]
    exact bakryEmeryGibbs_dirichlet W f g b (hW.of_le (by norm_num))
      (hf.of_le (by norm_num)) hg hc
  have hco : (∫ x, F x ⬝ᵥ H x *ᵥ F x ∂μ) ≤
      ∫ x, bakryEmeryGibbsGenerator W b f x^2 ∂μ := by
    rw [correspondenceBrascampLieb_integral_density W _ hW.continuous,
      correspondenceBrascampLieb_integral_density W _ hW.continuous]
    exact correspondenceBrascampLieb_hessian_coercivity W f b hW hf hc
  have he0 : 0 ≤ ∫ x, correspondenceBrascampLiebInverseEnergy W g b x ∂μ :=
    integral_nonneg fun x => by
      change 0 ≤ G x ⬝ᵥ (H x)⁻¹ *ᵥ G x
      simpa only [star_trivial] using
        (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg (G x)
  rw [hDir, neg_sq]
  exact hCS.trans (mul_le_mul_of_nonneg_left hco he0)

end
end GinibrePoincare
