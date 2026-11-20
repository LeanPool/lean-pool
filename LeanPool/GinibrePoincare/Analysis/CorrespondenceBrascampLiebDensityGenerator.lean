/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebDensityGenerator.lean.
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
/-!
# Correspondence Brascamp Lieb density generator

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem correspondenceBrascampLieb_density_derivative
    (W : E → ℝ) (hW : ContDiff ℝ 1 W) (v x : E) :
    bakryEmeryGibbsDirectional (bakryEmeryGibbsWeight W) v x =
      -bakryEmeryGibbsDirectional W v x * bakryEmeryGibbsWeight W x := by
  have hd := ((hW.differentiable (by norm_num) x).hasFDerivAt).neg.exp
  change HasFDerivAt (bakryEmeryGibbsWeight W) _ x at hd
  unfold bakryEmeryGibbsDirectional
  rw [hd.fderiv]
  simp [bakryEmeryGibbsWeight, mul_comm]

theorem correspondenceBrascampLieb_density_generator
    {ι : Type*} [Fintype ι] (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 1 W) (x : E) :
    bakryEmeryGibbsGenerator W b f x =
    (∑ i, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b i) x) +
    ∑ i, (bakryEmeryGibbsWeight W x)⁻¹ *
      bakryEmeryGibbsDirectional (bakryEmeryGibbsWeight W) (b i) x *
      bakryEmeryGibbsDirectional f (b i) x := by
  simp_rw [correspondenceBrascampLieb_density_derivative W hW]
  unfold bakryEmeryGibbsGenerator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hn : bakryEmeryGibbsWeight W x ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

end
end GinibrePoincare
