/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryCauchyGreenKernel.lean.
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
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticDbarBochner
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Correspondence auxiliary Cauchy Green kernel

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `cauchyGreenPotential_contDiff`, `cauchyGreenPotential_directional_derivative`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Convolution ContDiff
namespace GinibrePoincare
noncomputable section

/-- The genuine planar Cauchy–Green fundamental kernel, totalized at zero. -/
def cauchyGreenKernel (z : ℂ) : ℂ := (Real.pi : ℂ)⁻¹ * z⁻¹

theorem cauchyGreenKernel_locallyIntegrable : LocallyIntegrable cauchyGreenKernel volume := by
  apply locallyIntegrable_of_norm_le_rpow
    (E := ℂ) (C := Real.pi⁻¹) (α := (1 : ℝ))
  · norm_num [Complex.finrank_real_complex]
  · exact ae_of_all _ (fun z => by
      simp [cauchyGreenKernel, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Real.rpow_neg_one])
  · exact ((measurable_const.mul measurable_inv) : Measurable
      cauchyGreenKernel).aestronglyMeasurable
  · norm_num [Complex.finrank_real_complex]

/-- Actual Cauchy–Green integral for a planar source. -/
def cauchyGreenPotential (a : ℂ → ℂ) (z : ℂ) : ℂ :=
  (cauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] a) z

theorem cauchyGreenPotential_contDiff (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ContDiff ℝ ∞ (cauchyGreenPotential a) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable ha

theorem cauchyGreenPotential_directional_derivative (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z v : ℂ) :
    fderiv ℝ (cauchyGreenPotential a) z v =
      ∫ y : ℂ, cauchyGreenKernel y * fderiv ℝ a (z-y) v := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable (ha.of_le (by simp)) z
  change fderiv ℝ (cauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] a) z v = _
  rw [hd.fderiv]
  have hi := ((hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) cauchyGreenKernel_locallyIntegrable
    (ha.continuous_fderiv (by simp)) z).integrable
  rw [convolution, ContinuousLinearMap.integral_apply hi v]
  rfl

end
end GinibrePoincare
