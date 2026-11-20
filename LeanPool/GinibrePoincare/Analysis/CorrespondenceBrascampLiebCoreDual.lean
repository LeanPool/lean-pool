/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCoreDual.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCore
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebDuality
/-!
# Correspondence Brascamp Lieb core dual

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section

theorem correspondenceBrascampLieb_toLp_inner
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [mul_comm]

theorem correspondenceBrascampLieb_toLp_norm_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, correspondenceBrascampLieb_toLp_inner μ f f hf hf]
  simp only [pow_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_core_dual_bound
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W))
    (f : CorrespondenceBrascampLiebCompactTest E) :
    (inner ℝ (hgL2.toLp g) (correspondenceBrascampLiebCoreL2 W b hW f))^2 ≤
    (∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W) *
    ‖correspondenceBrascampLiebCoreL2 W b hW f‖^2 := by
  unfold correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner, correspondenceBrascampLieb_toLp_norm_sq]
  exact correspondenceBrascampLieb_compact_generator_bound W g f.val b hW hg
    (f.smooth.of_le (by norm_num)) f.compact hpos hgE

end
end GinibrePoincare
