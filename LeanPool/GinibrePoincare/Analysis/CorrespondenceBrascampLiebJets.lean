/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebJets.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsGenerator
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Correspondence Brascamp Lieb jets

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_direction_mul`.
-/

@[expose] public section
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem correspondenceBrascampLieb_direction_contDiff {f : E → ℝ} {m : ℕ∞ω}
    (hf : ContDiff ℝ (m + 1) f) (v : E) :
    ContDiff ℝ m (bakryEmeryGibbsDirectional f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem correspondenceBrascampLieb_direction_commute {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (v w : E) :
    bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f v) w =
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f w) v := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he (a b : E) :
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f a) b x =
        fderiv ℝ (fderiv ℝ f) x b a := by
    unfold bakryEmeryGibbsDirectional
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [he, he]
  exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num) w v

theorem correspondenceBrascampLieb_direction_mul {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) (x : E) :
    bakryEmeryGibbsDirectional (fun y => f y * g y) v x =
      bakryEmeryGibbsDirectional f v x * g x +
        f x * bakryEmeryGibbsDirectional g v x := by
  unfold bakryEmeryGibbsDirectional
  change (fderiv ℝ (f * g) x) v = _
  rw [fderiv_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  simp
  ring

theorem correspondenceBrascampLieb_direction_sub {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (v : E) (x : E) :
    bakryEmeryGibbsDirectional (fun y => f y - g y) v x =
      bakryEmeryGibbsDirectional f v x - bakryEmeryGibbsDirectional g v x := by
  unfold bakryEmeryGibbsDirectional
  change (fderiv ℝ (f - g) x) v = _
  rw [fderiv_sub (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  simp

end
end GinibrePoincare
