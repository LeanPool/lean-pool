/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebCore.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCompactBound
public import Mathlib.MeasureTheory.Function.L2Space
/-!
# Correspondence Brascamp Lieb core

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

/-- Smooth compactly supported real-valued test functions on `E`. -/
structure CorrespondenceBrascampLiebCompactTest (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The underlying function. -/
  val : E → ℝ
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [DecidableEq ι] in
theorem correspondenceBrascampLieb_generator_continuous
    (W f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 3 f) :
    Continuous (bakryEmeryGibbsGenerator W b f) := by
  classical
  apply continuous_finsetSum
  intro i _
  have hdf : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hddf : ContDiff ℝ 1
      (bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 1) hdf (b i)
  have hdW : ContDiff ℝ 1 (bakryEmeryGibbsDirectional W (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)
  exact hddf.continuous.sub (hdW.continuous.mul hdf.continuous)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [DecidableEq ι] in
theorem correspondenceBrascampLieb_generator_compact
    (W f : E → ℝ) (b : ι → E) (hc : HasCompactSupport f) :
    HasCompactSupport (bakryEmeryGibbsGenerator W b f) := by
  classical
  have hs : HasCompactSupport (∑ i, fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
      bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x) := by
    apply HasCompactSupport.finset_sum
    intro i _
    exact ((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)).sub
      ((hc.fderiv_apply ℝ (b i)).mul_left)
  have he : (∑ i, fun x =>
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x -
      bakryEmeryGibbsDirectional W (b i) x * bakryEmeryGibbsDirectional f (b i) x) =
      bakryEmeryGibbsGenerator W b f := by
    funext x
    simp only [Finset.sum_apply, bakryEmeryGibbsGenerator]
  rw [he] at hs
  exact hs

omit [DecidableEq ι] in
omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_generator_memLp
    (W f : E → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    MemLp (bakryEmeryGibbsGenerator W b f) 2 (correspondenceBrascampLiebMeasure W) := by
  classical
  have hL := correspondenceBrascampLieb_generator_continuous W f b hW hf
  have hLc := correspondenceBrascampLieb_generator_compact W f b hc
  apply (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mpr
  exact correspondenceBrascampLieb_integrable_compact W _ hW.continuous
    (hL.norm.pow 2) (by
      apply hLc.mono
      intro x hx hz
      apply hx
      simp [hz])

/-- The `L²(correspondenceBrascampLiebMeasure W)` class of the Gibbs generator
`bakryEmeryGibbsGenerator W b` applied to a compact test function `f`. -/
def correspondenceBrascampLiebCoreL2 (W : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 2 W) (f : CorrespondenceBrascampLiebCompactTest E) :
    Lp ℝ 2 (correspondenceBrascampLiebMeasure W) :=
  (correspondenceBrascampLieb_generator_memLp W f.val b hW
    (f.smooth.of_le (by norm_num)) f.compact).toLp _

end
end GinibrePoincare
