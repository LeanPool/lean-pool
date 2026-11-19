/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenHomotopy.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenSmoothSolver

/-!
# Correspondence auxiliary Cauchy Green homotopy

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreen_cutoff_homotopy`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section

/-- The actual Cauchy–Green homotopy on smooth compact functions. -/
theorem cauchyGreenPotential_dbar_source (f : ℂ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : ℂ) :
    cauchyGreenPotential (planarDbar f) z = f z := by
  let θ : ℂ → ℂ := fun y => f (z-y)
  have hθ : ContDiff ℝ 1 θ := (hf.of_le (by simp)).comp
    (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have h := cauchyGreenKernel_fundamental_identity θ hθ hcθ
  have hder (y : ℂ) : planarDbar θ y = -planarDbar f (z-y) :=
    planarDbar_sub_left f (hf.differentiable (by simp)) z y
  simp_rw [hder, mul_neg, integral_neg] at h
  have hh := neg_injective h
  simpa only [cauchyGreenPotential, convolution, ContinuousLinearMap.mul_apply', θ, sub_zero] using!
      hh

theorem planarDbar_mul (f g : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    planarDbar (f*g) z = planarDbar f z * g z + f z * planarDbar g z := by
  rw [planarDbar, fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul, planarDbar]
  ring

/-- The literal boundary correction formula. Its right-hand side contains
no derivative of the rough source, enabling the L² local homotopy. -/
theorem cauchyGreen_cutoff_homotopy (χ g : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : ContDiff ℝ ∞ g) (z : ℂ) :
    cauchyGreenPotential (fun w => χ w * planarDbar g w) z =
      χ z * g z - cauchyGreenPotential (fun w => planarDbar χ w * g w) z := by
  have hχg : HasCompactSupport (χ*g) := hc.mul_right
  have h := cauchyGreenPotential_dbar_source (χ*g) (hχ.mul hg) hχg z
  have he : planarDbar (χ*g) =
      (fun w => planarDbar χ w * g w) + (fun w => χ w * planarDbar g w) := by
    funext w
    exact planarDbar_mul χ g (hχ.differentiable (by simp)) (hg.differentiable (by simp)) w
  have hci : HasCompactSupport (fun w => planarDbar χ w * g w) :=
    (planarDbar_compact χ hc).mul_right
  have hcj : HasCompactSupport (fun w => χ w * planarDbar g w) := hc.mul_right
  have hi := (hci.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable
      ((planarDbar_continuous χ (hχ.of_le (by simp))).mul hg.continuous) z).integrable
  have hj := (hcj.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable
      (hχ.continuous.mul (planarDbar_continuous g (hg.of_le (by simp)))) z).integrable
  rw [he] at h
  simp only [ContinuousLinearMap.mul_apply'] at hi hj
  simp only [cauchyGreenPotential, convolution, Pi.add_apply, ContinuousLinearMap.mul_apply',
      mul_add] at h
  rw [integral_add hi hj] at h
  change _ = χ z * g z at h
  change _ = χ z * g z - _
  exact eq_sub_of_add_eq' h

end
end GinibrePoincare
