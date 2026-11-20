/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeakDual.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakBound
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCenter
/-!
# Correspondence Brascamp Lieb weak dual

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

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_weak_centered_core_bound
    (W u : E → ℝ) (G : E → ι → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hE : Integrable (correspondenceBrascampLiebWeakInverseEnergy W G b)
      (correspondenceBrascampLiebMeasure W))
    (f : CorrespondenceBrascampLiebCompactTest E) :
    (inner ℝ ((correspondenceBrascampLieb_center_memLp W u hu).toLp
        (correspondenceBrascampLiebCenter W u)) (correspondenceBrascampLiebCoreL2 W b hW f))^2 ≤
    (∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x ∂correspondenceBrascampLiebMeasure W)*
      ‖correspondenceBrascampLiebCoreL2 W b hW f‖^2 := by
  let μ := correspondenceBrascampLiebMeasure W
  let L := bakryEmeryGibbsGenerator W b f.val
  have hLp : MemLp L 2 μ := correspondenceBrascampLieb_generator_memLp W f.val b hW
    (f.smooth.of_le (by norm_num)) f.compact
  have hiu : Integrable (fun x => u x*L x) μ := hu.integrable_mul hLp
  have hiL : Integrable L μ := hLp.integrable (by norm_num)
  have hstat : (∫ x, L x ∂μ) = 0 := by
    rw [correspondenceBrascampLieb_integral_density W _ hW.continuous]
    exact bakryEmeryGibbs_core_stationarity W f.val b (hW.of_le (by norm_num))
      (f.smooth.of_le (by norm_num)) f.compact
  have hcenter : (∫ x, correspondenceBrascampLiebCenter W u x*L x ∂μ) =
      ∫ x, u x*L x ∂μ := by
    unfold correspondenceBrascampLiebCenter
    simp_rw [sub_mul]
    rw [integral_sub hiu (hiL.const_mul _), integral_const_mul, hstat]
    ring
  unfold correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner, correspondenceBrascampLieb_toLp_norm_sq]
  rw [hcenter]
  exact correspondenceBrascampLieb_weak_compact_bound W u f.val G b hW hu hG hw hpos hE
    (f.smooth.of_le (by norm_num)) f.compact

end
end GinibrePoincare
