/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebHessian.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebBochnerIntegral
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebMatrix
/-!
# Correspondence Brascamp Lieb hessian

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_hessian_coercivity`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

/-- The Hessian matrix of `W` at `x` in the directions `b`, with entries `∂_{b j} ∂_{b i} W x`. -/
def correspondenceBrascampLiebHessian (W : E → ℝ) (b : ι → E) (x : E) : Matrix ι ι ℝ :=
  fun i j => bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x

/-- The gradient coordinates `i ↦ ∂_{b i} f x` of `f` at `x` in the directions `b`. -/
def correspondenceBrascampLiebGradient (f : E → ℝ) (b : ι → E) (x : E) : ι → ℝ :=
  fun i => bakryEmeryGibbsDirectional f (b i) x

omit [CompleteSpace E] in
/-- Concrete variable-Hessian coercivity, prior to any use of range density. -/
theorem correspondenceBrascampLieb_hessian_coercivity
    (W f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, correspondenceBrascampLiebGradient f b x ⬝ᵥ
      correspondenceBrascampLiebHessian W b x *ᵥ correspondenceBrascampLiebGradient f b x *
      bakryEmeryGibbsWeight W x) ≤
    ∫ x, bakryEmeryGibbsGenerator W b f x ^ 2 * bakryEmeryGibbsWeight W x := by
  have hW1 (i : ι) : ContDiff ℝ 1 (bakryEmeryGibbsDirectional W (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)
  have hf2 (i : ι) : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hH (i j : ι) : Continuous
      (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j)) :=
    ((hW1 i).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  have hw : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hi (i j : ι) : Integrable (fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
      bakryEmeryGibbsWeight W x) :=
    ((((hH i j).mul (hf2 i).continuous).mul (hf2 j).continuous).mul
        hw).integrable_of_hasCompactSupport
        ((hc.fderiv_apply ℝ (b i)).mul_left.mul_right.mul_right)
  have he : (∫ x, correspondenceBrascampLiebGradient f b x ⬝ᵥ
      correspondenceBrascampLiebHessian W b x *ᵥ correspondenceBrascampLiebGradient f b x *
      bakryEmeryGibbsWeight W x) =
      ∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
      bakryEmeryGibbsWeight W x := by
    have hp (x : E) : correspondenceBrascampLiebGradient f b x ⬝ᵥ
        correspondenceBrascampLiebHessian W b x *ᵥ correspondenceBrascampLiebGradient f b x *
        bakryEmeryGibbsWeight W x = ∑ i, ∑ j,
        bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
        bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
        bakryEmeryGibbsWeight W x := by
      simp only [dotProduct, Matrix.mulVec, correspondenceBrascampLiebGradient,
        correspondenceBrascampLiebHessian, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hp]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hi i j)
    · intro i _
      exact integrable_finsetSum _ (fun j _ => hi i j)
  rw [he, correspondenceBrascampLieb_bochner_integral W f b hW hf hc]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

end
end GinibrePoincare
