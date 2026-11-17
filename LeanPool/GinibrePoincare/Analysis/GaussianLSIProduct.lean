/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianLSIProduct.lean.
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

public import Mathlib.Analysis.Calculus.Deriv.Prod

public import LeanPool.GinibrePoincare.Analysis.GaussianLSIScaling
public import LeanPool.GinibrePoincare.Analysis.IntegralEntropyTensorization

/-!
# Gaussian LSIProduct
-/


@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Coordinate derivatives in the real two-dimensional Gaussian product. -/
def gaussianPartialLeft (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (1, 0)
def gaussianPartialRight (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (0, 1)

theorem deriv_gaussian_fiber_left (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x y : ℝ) :
    deriv (fun t => f (t, y)) x = gaussianPartialLeft f (x, y) := by
  simpa only [Function.comp_def, id_eq, gaussianPartialLeft] using
    (((hf.differentiable one_ne_zero (x, y)).hasFDerivAt).comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

theorem deriv_gaussian_fiber_right (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (x y : ℝ) :
    deriv (fun t => f (x, t)) y = gaussianPartialRight f (x, y) := by
  simpa only [Function.comp_def, id_eq, gaussianPartialRight] using
    (((hf.differentiable one_ne_zero (x, y)).hasFDerivAt).comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

/-- The sharp two-coordinate Gaussian LSI for bounded C¹ observables with
bounded derivative, proved by the integral entropy tensorization inequality. -/
theorem gaussianReal_prod_lsi_bounded_C1 (v w : ℝ≥0) (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (C D : ℝ) (hC : 0 ≤ C)
    (hb : ∀ p, |f p| ≤ C) (hd : ∀ p, ‖fderiv ℝ f p‖ ≤ D) :
    squareEntropy ((gaussianReal 0 v).prod (gaussianReal 0 w)) f ≤
      (2 * (v : ℝ)) * ∫ p, gaussianPartialLeft f p ^ 2
        ∂(gaussianReal 0 v).prod (gaussianReal 0 w) +
      (2 * (w : ℝ)) * ∫ p, gaussianPartialRight f p ^ 2
        ∂(gaussianReal 0 v).prod (gaussianReal 0 w) := by
  let μ := gaussianReal 0 v
  let ν := gaussianReal 0 w
  have hL : Continuous (gaussianPartialLeft f) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hR : Continuous (gaussianPartialRight f) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hLb (p : ℝ × ℝ) : |gaussianPartialLeft f p| ≤ D := by
    have h := (fderiv ℝ f p).le_opNorm (1, 0)
    simpa [gaussianPartialLeft] using h.trans (by simpa using hd p)
  have hRb (p : ℝ × ℝ) : |gaussianPartialRight f p| ≤ D := by
    have h := (fderiv ℝ f p).le_opNorm (0, 1)
    simpa [gaussianPartialRight] using h.trans (by simpa using hd p)
  have hLb2 (p : ℝ × ℝ) : gaussianPartialLeft f p ^ 2 ∈ Set.Icc 0 (D ^ 2) := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [hLb p, abs_nonneg (gaussianPartialLeft f p), sq_abs (gaussianPartialLeft f p)]
  have hRb2 (p : ℝ × ℝ) : gaussianPartialRight f p ^ 2 ∈ Set.Icc 0 (D ^ 2) := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [hRb p, abs_nonneg (gaussianPartialRight f p), sq_abs (gaussianPartialRight f p)]
  have hLi : Integrable (fun p => gaussianPartialLeft f p ^ 2) (μ.prod ν) :=
    memLp_one_iff_integrable.mp (memLp_of_bounded (Eventually.of_forall hLb2)
      (hL.pow 2).aestronglyMeasurable 1)
  have hRi : Integrable (fun p => gaussianPartialRight f p ^ 2) (μ.prod ν) :=
    memLp_one_iff_integrable.mp (memLp_of_bounded (Eventually.of_forall hRb2)
      (hR.pow 2).aestronglyMeasurable 1)
  have hleft (y : ℝ) :
      0 ≤ squareEntropy μ (fun x => f (x, y)) ∧
      squareEntropy μ (fun x => f (x, y)) ≤
        (2 * (v : ℝ)) * ∫ x, gaussianPartialLeft f (x, y) ^ 2 ∂μ := by
    have hcf : ContDiff ℝ 1 (fun x => f (x, y)) := hf.comp (by fun_prop)
    have hvf : MemLp (fun x => f (x, y)) 2 μ :=
      MemLp.of_bound hcf.continuous.aestronglyMeasurable C
        (Eventually.of_forall (fun x => by simpa using hb (x, y)))
    have hdf : MemLp (deriv (fun x => f (x, y))) 2 μ := by
      apply MemLp.of_bound (hcf.continuous_deriv le_rfl).aestronglyMeasurable D
      apply Eventually.of_forall
      intro x
      simpa [deriv_gaussian_fiber_left f hf x y] using hLb (x, y)
    have he := gaussianReal_lsi_variance_C1 v _ hcf hvf hdf
    constructor
    · exact squareEntropy_nonneg μ _ (by
        simpa [Real.norm_eq_abs, sq_abs] using
          hvf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) he.1
    · simpa only [deriv_gaussian_fiber_left f hf] using he.2
  have hright (x : ℝ) :
      0 ≤ squareEntropy ν (fun y => f (x, y)) ∧
      squareEntropy ν (fun y => f (x, y)) ≤
        (2 * (w : ℝ)) * ∫ y, gaussianPartialRight f (x, y) ^ 2 ∂ν := by
    have hcf : ContDiff ℝ 1 (fun y => f (x, y)) := hf.comp (by fun_prop)
    have hvf : MemLp (fun y => f (x, y)) 2 ν :=
      MemLp.of_bound hcf.continuous.aestronglyMeasurable C
        (Eventually.of_forall (fun y => by simpa using hb (x, y)))
    have hdf : MemLp (deriv (fun y => f (x, y))) 2 ν := by
      apply MemLp.of_bound (hcf.continuous_deriv le_rfl).aestronglyMeasurable D
      apply Eventually.of_forall
      intro y
      simpa [deriv_gaussian_fiber_right f hf x y] using hRb (x, y)
    have he := gaussianReal_lsi_variance_C1 w _ hcf hvf hdf
    constructor
    · exact squareEntropy_nonneg ν _ (by
        simpa [Real.norm_eq_abs, sq_abs] using
          hvf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) he.1
    · simpa only [deriv_gaussian_fiber_right f hf] using he.2
  have hiL := integral_mono_of_nonneg (Eventually.of_forall (fun y => (hleft y).1))
    (hLi.integral_prod_right.const_mul (2 * (v : ℝ)))
    (Eventually.of_forall (fun y => (hleft y).2))
  have hiR := integral_mono_of_nonneg (Eventually.of_forall (fun x => (hright x).1))
    (hRi.integral_prod_left.const_mul (2 * (w : ℝ)))
    (Eventually.of_forall (fun x => (hright x).2))
  rw [integral_const_mul, ← integral_prod_symm _ hLi] at hiL
  rw [integral_const_mul, ← integral_prod _ hRi] at hiR
  have ht := squareEntropy_prod_tensorization_bounded μ ν f hf.continuous.measurable C hC hb
  exact ht.trans (by linarith)

/-- In particular the Gaussian product inequality is unconditional on the compact
C¹ core, with the sharp coefficient in each coordinate. -/
theorem gaussianReal_prod_lsi_C1 (v w : ℝ≥0) (f : ℝ × ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    squareEntropy ((gaussianReal 0 v).prod (gaussianReal 0 w)) f ≤
      (2 * (v : ℝ)) * ∫ p, gaussianPartialLeft f p ^ 2
        ∂(gaussianReal 0 v).prod (gaussianReal 0 w) +
      (2 * (w : ℝ)) * ∫ p, gaussianPartialRight f p ^ 2
        ∂(gaussianReal 0 v).prod (gaussianReal 0 w) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  apply gaussianReal_prod_lsi_bounded_C1 v w f hf |C| D (abs_nonneg C)
  · intro p
    exact (hC p).trans (le_abs_self C)
  · exact hD

end
end GinibrePoincare
