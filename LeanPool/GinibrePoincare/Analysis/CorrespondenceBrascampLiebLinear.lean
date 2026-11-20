/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebLinear.lean.
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
/-!
# Correspondence Brascamp Lieb linear

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem correspondenceBrascampLieb_direction_add {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) :
    bakryEmeryGibbsDirectional (f+g) v =
      bakryEmeryGibbsDirectional f v + bakryEmeryGibbsDirectional g v := by
  funext x
  unfold bakryEmeryGibbsDirectional
  rw [fderiv_add (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
  simp

theorem correspondenceBrascampLieb_direction_smul {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (c : ℝ) (v : E) :
    bakryEmeryGibbsDirectional (c • f) v = c • bakryEmeryGibbsDirectional f v := by
  funext x
  unfold bakryEmeryGibbsDirectional
  rw [fderiv_const_smul (hf.differentiable (by norm_num) x)]
  simp

variable {ι : Type*} [Fintype ι]
theorem correspondenceBrascampLieb_generator_add
    (W f g : E → ℝ) (b : ι → E) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    bakryEmeryGibbsGenerator W b (f+g) =
      bakryEmeryGibbsGenerator W b f + bakryEmeryGibbsGenerator W b g := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  funext x
  unfold bakryEmeryGibbsGenerator
  simp_rw [correspondenceBrascampLieb_direction_add hf1 hg1]
  simp_rw [correspondenceBrascampLieb_direction_add
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hf _)
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hg _)]
  simp only [Pi.add_apply]
  simp_rw [mul_add, add_sub_add_comm, Finset.sum_add_distrib]

theorem correspondenceBrascampLieb_generator_smul
    (W f : E → ℝ) (b : ι → E) (hf : ContDiff ℝ 2 f) (c : ℝ) :
    bakryEmeryGibbsGenerator W b (c • f) = c • bakryEmeryGibbsGenerator W b f := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  funext x
  unfold bakryEmeryGibbsGenerator
  simp_rw [correspondenceBrascampLieb_direction_smul hf1 c]
  simp_rw [correspondenceBrascampLieb_direction_smul
    (correspondenceBrascampLieb_direction_contDiff (m := 1) hf _) c]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end GinibrePoincare
