/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenPotential.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenIBP

/-!
# Correspondence auxiliary Cauchy Green potential

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenPotential_dbar_integral`, `planarDbar_sub_left`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem cauchyGreenPotential_dbar_integral (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z : ℂ) :
    planarDbar (cauchyGreenPotential a) z =
      ∫ y : ℂ, cauchyGreenKernel y * planarDbar a (z-y) := by
  have hi (v : ℂ) : Integrable (fun y : ℂ => cauchyGreenKernel y * fderiv ℝ a (z-y) v) volume :=
    ((hc.fderiv_apply ℝ v).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      cauchyGreenKernel_locallyIntegrable
      ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) z).integrable
  change (1/2 : ℂ)*(fderiv ℝ (cauchyGreenPotential a) z 1 +
    Complex.I*fderiv ℝ (cauchyGreenPotential a) z Complex.I) = _
  rw [cauchyGreenPotential_directional_derivative a ha hc z 1,
    cauchyGreenPotential_directional_derivative a ha hc z Complex.I]
  rw [← integral_const_mul,← integral_add (hi 1) ((hi Complex.I).const_mul Complex.I),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by unfold planarDbar; ring)

theorem planarDbar_sub_left (a : ℂ → ℂ) (ha : Differentiable ℝ a) (z y : ℂ) :
    planarDbar (fun w : ℂ => a (z-w)) y = -planarDbar a (z-y) := by
  have hd := (ha (z-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
  have he : (fun w : ℂ => a (z-w)) = a ∘ (fun w : ℂ => z-w) := rfl
  simp only [planarDbar, he, hd.fderiv, ContinuousLinearMap.comp_apply,
    
    ContinuousLinearMap.id_apply, neg_apply, zero_sub, map_neg]
  ring

end
end GinibrePoincare
