/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebConstants.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCoreRange
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCoreDual
/-!
# Correspondence Brascamp Lieb constants

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_constants_orthogonal`,
`correspondenceBrascampLieb_closed_core_bound`.
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

/-- The constant function `1` as an element of `L²(correspondenceBrascampLiebMeasure W)`. -/
def correspondenceBrascampLiebOneL2 (W : E → ℝ)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    Lp ℝ 2 (correspondenceBrascampLiebMeasure W) :=
  (memLp_const (μ := correspondenceBrascampLiebMeasure W) (p := 2) (1 : ℝ)).toLp (fun _ => 1)

omit [CompleteSpace E] [DecidableEq ι] in
theorem correspondenceBrascampLieb_constants_orthogonal
    (W : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    (ℝ ∙ correspondenceBrascampLiebOneL2 W) ≤
      (correspondenceBrascampLiebCoreRange W b hW)ᗮ := by
  classical
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨f, rfl⟩
  unfold correspondenceBrascampLiebOneL2 correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner]
  simp only [mul_one]
  rw [correspondenceBrascampLieb_integral_density W _ hW.continuous]
  exact bakryEmeryGibbs_core_stationarity W f.val b (hW.of_le (by norm_num))
    (f.smooth.of_le (by norm_num)) f.compact

omit [CompleteSpace E] in
/-- Final Hilbert dual step once centered-range membership has been obtained
from the concrete weighted elliptic theorem. This is an internal reduction. -/
theorem correspondenceBrascampLieb_closed_core_bound
    (W g : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hgL2 : MemLp g 2 (correspondenceBrascampLiebMeasure W))
    (hgE : Integrable (correspondenceBrascampLiebInverseEnergy W g b)
      (correspondenceBrascampLiebMeasure W))
    (hu : hgL2.toLp g ∈ (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure) :
    (∫ x, g x^2 ∂correspondenceBrascampLiebMeasure W) ≤
      ∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W := by
  rw [← correspondenceBrascampLieb_toLp_norm_sq _ g hgL2]
  apply correspondenceBrascampLieb_duality (hgL2.toLp g)
    (correspondenceBrascampLiebCoreRange W b hW)
    (∫ x, correspondenceBrascampLiebInverseEnergy W g b x
      ∂correspondenceBrascampLiebMeasure W)
  · apply integral_nonneg
    intro x
    change 0 ≤ correspondenceBrascampLiebGradient g b x ⬝ᵥ
      (correspondenceBrascampLiebHessian W b x)⁻¹ *ᵥ correspondenceBrascampLiebGradient g b x
    simpa only [star_trivial] using
      (hpos x).posSemidef.inv.dotProduct_mulVec_nonneg (correspondenceBrascampLiebGradient g b x)
  · exact hu
  · rintro _ ⟨f, rfl⟩
    exact correspondenceBrascampLieb_core_dual_bound W g b hW hg hpos hgL2 hgE f

end
end GinibrePoincare
