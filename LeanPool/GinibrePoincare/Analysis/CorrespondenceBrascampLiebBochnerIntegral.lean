/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebBochnerIntegral.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebBochner
/-!
# Correspondence Brascamp Lieb Bochner integral

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_bochner_integral`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

omit [CompleteSpace E] in
/-- Literal weighted generator-square identity, with every analytic
integration input supplied by smoothness and compact support. -/
theorem correspondenceBrascampLieb_bochner_integral
    {ι : Type*} [Fintype ι] (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, bakryEmeryGibbsGenerator W b f x ^ 2 * bakryEmeryGibbsWeight W x) =
    (∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b j) x ^ 2 *
      bakryEmeryGibbsWeight W x) +
    ∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
      bakryEmeryGibbsWeight W x := by
  let A (i : ι) := correspondenceBrascampLiebAdjoint W
    (bakryEmeryGibbsDirectional f (b i)) (b i)
  have hdf (i : ι) : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f (b i)) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hA (i : ι) : Continuous (A i) :=
    (correspondenceBrascampLieb_adjoint_contDiff W _ _ hW (hdf i)).continuous
  have hAc (i : ι) : HasCompactSupport (A i) := by
    exact ((hc.fderiv_apply ℝ (b i)).mul_left).sub
      ((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i))
  have hweight : Continuous (bakryEmeryGibbsWeight W) :=
    Real.continuous_exp.comp hW.continuous.neg
  have hi (i j : ι) : Integrable (fun x => A i x * A j x * bakryEmeryGibbsWeight W x) :=
    (((hA i).mul (hA j)).mul hweight).integrable_of_hasCompactSupport
      ((hAc i).mul_right.mul_right)
  have hp (x : E) : bakryEmeryGibbsGenerator W b f x ^ 2 * bakryEmeryGibbsWeight W x =
      ∑ i, ∑ j, A i x * A j x * bakryEmeryGibbsWeight W x := by
    have hL : bakryEmeryGibbsGenerator W b f x = -(∑ i, A i x) := by
      simp only [bakryEmeryGibbsGenerator, A, correspondenceBrascampLiebAdjoint]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hL]
    calc
      _ = (∑ i, A i x) * ((∑ j, A j x) * bakryEmeryGibbsWeight W x) := by ring
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
  calc
    _ = ∫ x, ∑ i, ∑ j, A i x * A j x * bakryEmeryGibbsWeight W x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hp x
    _ = ∑ i, ∑ j, ∫ x, A i x * A j x * bakryEmeryGibbsWeight W x := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => hi i j)
      · intro i _
        exact integrable_finsetSum _ (fun j _ => hi i j)
    _ = _ := correspondenceBrascampLieb_bochner_sum W f b hW hf hc

end
end GinibrePoincare
