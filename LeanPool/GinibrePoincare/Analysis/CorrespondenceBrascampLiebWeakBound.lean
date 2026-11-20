/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeakBound.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakDirichlet
/-!
# Correspondence Brascamp Lieb weak bound

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse-Hessian energy `G x ⬝ᵥ (∇²W x)⁻¹ *ᵥ G x` of a coordinate field `G`, with the
Hessian taken in the directions `b`. -/
def correspondenceBrascampLiebWeakInverseEnergy (W : E → ℝ) (G : E → ι → ℝ)
    (b : ι → E) (x : E) : ℝ :=
  G x ⬝ᵥ (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ G x

omit [CompleteSpace E] [IsAddHaarMeasure (volume : Measure E)] in
theorem correspondenceBrascampLieb_localL2_integrable_test
    (W G θ : E → ℝ) (hW : Continuous W) (hG : CorrespondenceBrascampLiebLocallyL2 G)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    Integrable (fun x => G x*θ x) (correspondenceBrascampLiebMeasure W) := by
  have hρ : Continuous (bakryEmeryGibbsWeight W) := Real.continuous_exp.comp hW.neg
  apply (correspondenceWeightedElliptic_integrable_density (bakryEmeryGibbsWeight W) _ hρ
    (fun _ => Real.exp_pos _)).mpr
  have he := (correspondenceBrascampLieb_localL2_locallyIntegrable G
    hG).integrable_smul_right_of_hasCompactSupport (hρ.mul hθ) hc.mul_left
  simpa only [Pi.mul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using he

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_weak_compact_bound
    (W u f : E → ℝ) (G : E → ι → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hE : Integrable (correspondenceBrascampLiebWeakInverseEnergy W G b)
      (correspondenceBrascampLiebMeasure W))
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, u x*bakryEmeryGibbsGenerator W b f x ∂correspondenceBrascampLiebMeasure W)^2 ≤
    (∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x ∂correspondenceBrascampLiebMeasure W)*
      (∫ x, bakryEmeryGibbsGenerator W b f x^2 ∂correspondenceBrascampLiebMeasure W) := by
  let μ := correspondenceBrascampLiebMeasure W
  let F := correspondenceBrascampLiebGradient f b
  let H := correspondenceBrascampLiebHessian W b
  have hiF : Integrable (fun x => F x ⬝ᵥ H x *ᵥ F x) μ :=
    correspondenceBrascampLieb_gradient_quadratic_integrable W f b H hW.continuous
      (hf.of_le (by norm_num)) hc (correspondenceBrascampLieb_hessian_continuous W b hW)
  have hiGF : Integrable (fun x => G x ⬝ᵥ F x) μ := by
    unfold dotProduct
    apply integrable_finsetSum
    intro i _
    exact correspondenceBrascampLieb_localL2_integrable_test W (fun x => G x i)
      (bakryEmeryGibbsDirectional f (b i)) hW.continuous (hG i)
      ((correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)).continuous)
      (hc.fderiv_apply ℝ (b i))
  have hCS := correspondenceBrascampLieb_integral_inverse_hessian μ H G F hpos hE hiF hiGF
  have hco : (∫ x, F x ⬝ᵥ H x *ᵥ F x ∂μ) ≤
      ∫ x, bakryEmeryGibbsGenerator W b f x^2 ∂μ := by
    rw [correspondenceBrascampLieb_integral_density W _ hW.continuous,
      correspondenceBrascampLieb_integral_density W _ hW.continuous]
    exact correspondenceBrascampLieb_hessian_coercivity W f b hW hf hc
  have he0 : 0 ≤ ∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x ∂μ :=
    integral_nonneg fun x => by
      change 0 ≤ G x ⬝ᵥ (H x)⁻¹ *ᵥ G x
      simpa only [star_trivial] using (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg (G x)
  rw [correspondenceBrascampLieb_weak_dirichlet W u f G b hW hu hG hw hf hc, neg_sq]
  exact hCS.trans (mul_le_mul_of_nonneg_left hco he0)

end
end GinibrePoincare
