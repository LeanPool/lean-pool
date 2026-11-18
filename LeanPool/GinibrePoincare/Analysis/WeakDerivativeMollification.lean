/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/WeakDerivativeMollification.lean.
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

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth convolution of ordinary weak directional derivatives

This reusable result concerns actual locally integrable functions and their
test-function weak derivative identity under an additive translation- and negation-invariant
  measure.
-/


@[expose] public section


open MeasureTheory MeasureTheory.Measure ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- Differentiating a genuine smooth compact convolution transfers an ordinary
weak directional derivative to convolution of that weak derivative. -/
theorem weakDirectionalDerivative_convolution (u g φ : E → ℝ) (v : E)
    (hu : LocallyIntegrable u μ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, g y * θ y ∂μ) = -(∫ y, u y * fderiv ℝ θ y v ∂μ)) (x : E) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) x v =
      (φ ⋆[lsmul ℝ ℝ, μ] g) x := by
  let θ : E → ℝ := fun y => φ (x - y)
  have ht : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y : E) : fderiv ℝ θ y v = - fderiv ℝ φ (x - y) v := by
    have hder := (hφ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [show θ = φ ∘ (fun y : E => x - y) from rfl, hder.fderiv]
    simp
  have he := hw θ ht htc
  simp_rw [hd, mul_neg] at he
  rw [integral_neg, neg_neg] at he
  have hder := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [hder.fderiv, convolution_eq_swap]
  have hi := ((hc.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL E) (hφ.continuous_fderiv (by simp)) hu x).integrable_swap
  rw [ContinuousLinearMap.integral_apply hi v, convolution_lsmul_swap]
  simp only [precompL_apply, lsmul_apply, smul_eq_mul]
  calc
    (∫ y, fderiv ℝ φ (x - y) v * u y ∂μ) =
        ∫ y, u y * fderiv ℝ φ (x - y) v ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => mul_comm _ _)
    _ = ∫ y, φ (x - y) * g y ∂μ := by
      rw [← he]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- Both the value convolution and the transferred derivative convolution are smooth. -/
theorem weakDirectionalDerivative_smooth_mollification (u g φ : E → ℝ) (v : E)
    (hu : LocallyIntegrable u μ) (hg : LocallyIntegrable g μ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, g y * θ y ∂μ) = -(∫ y, u y * fderiv ℝ θ y v ∂μ)) :
    ContDiff ℝ ∞ (φ ⋆[lsmul ℝ ℝ, μ] u) ∧
      ContDiff ℝ ∞ (φ ⋆[lsmul ℝ ℝ, μ] g) ∧
      ∀ x, fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) x v =
        (φ ⋆[lsmul ℝ ℝ, μ] g) x :=
  ⟨hc.contDiff_convolution_left _ hφ hu, hc.contDiff_convolution_left _ hφ hg,
    weakDirectionalDerivative_convolution μ u g φ v hu hφ hc hw⟩

end
end GinibrePoincare
