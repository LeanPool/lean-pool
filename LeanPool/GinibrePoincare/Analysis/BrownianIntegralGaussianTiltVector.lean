/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltVector.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltNonnegative
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Brownian integral Gaussian tilt vector

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianVectorExponentialTilt_eq_exp`, `gaussianVectorExponentialTilt_lintegral`,
`gaussianVectorExponentialTilt_lintegral_sq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The coordinatewise product `∏ i, gaussianExponentialTilt (h i) v (x i)` of scalar Gaussian
exponential tilts. -/
def gaussianVectorExponentialTilt {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) (x : ι → ℝ) : ℝ :=
  ∏ i, gaussianExponentialTilt (h i) v (x i)

theorem gaussianVectorExponentialTilt_eq_exp {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) (x : ι → ℝ) :
    gaussianVectorExponentialTilt h v x =
      Real.exp (∑ i, (h i*x i-(h i)^2*(v : ℝ)/2)) := by
  classical
  simp only [gaussianVectorExponentialTilt, gaussianExponentialTilt, Real.exp_sum]

theorem gaussianVectorExponentialTilt_nonneg {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) (x : ι → ℝ) : 0≤gaussianVectorExponentialTilt h v x := by
  classical
  apply Finset.prod_nonneg
  intro i hi
  exact (Real.exp_pos _).le

theorem gaussianVectorExponentialTilt_integrable {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    Integrable (gaussianVectorExponentialTilt h v) (Measure.pi (fun _ : ι => gaussianReal 0 v)) :=
  Integrable.fintype_prod_dep (fun i => gaussianExponentialTilt_integrable (h i) v)

theorem gaussianVectorExponentialTilt_sq_integrable {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun x => (gaussianVectorExponentialTilt h v x)^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 v)) := by
  classical
  simp_rw [gaussianVectorExponentialTilt,← Finset.prod_pow]
  exact Integrable.fintype_prod_dep (fun i => gaussianExponentialTilt_sq_integrable (h i) v)

theorem gaussianVectorExponentialTilt_integral {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (∫ x, gaussianVectorExponentialTilt h v x ∂Measure.pi (fun _ : ι => gaussianReal 0 v))=1 := by
  classical
  unfold gaussianVectorExponentialTilt
  rw [integral_fintype_prod_eq_prod]
  simp only [gaussianExponentialTilt_integral, Finset.prod_const_one]

theorem gaussianVectorExponentialTilt_integral_sq {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (∫ x, (gaussianVectorExponentialTilt h v x)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 v))=
      Real.exp ((∑ i, (h i)^2)*(v : ℝ)) := by
  classical
  simp_rw [gaussianVectorExponentialTilt,← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (μ:=fun _ : ι => gaussianReal 0 v)
    (fun i x => (gaussianExponentialTilt (h i) v x)^2)]
  simp only [gaussianExponentialTilt_integral_sq,← Real.exp_sum, Finset.sum_mul]

theorem gaussianVectorExponentialTilt_lintegral {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (∫⁻ x, ENNReal.ofReal (gaussianVectorExponentialTilt h v x)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 v))=1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianVectorExponentialTilt_integrable h v)
    (Eventually.of_forall (gaussianVectorExponentialTilt_nonneg h v)),
        gaussianVectorExponentialTilt_integral]
  exact ENNReal.ofReal_one

theorem gaussianVectorExponentialTilt_lintegral_sq {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (∫⁻ x, ENNReal.ofReal (gaussianVectorExponentialTilt h v x)^2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 v))=
      ENNReal.ofReal (Real.exp ((∑ i, (h i)^2)*(v : ℝ))) := by
  have he (x : ι → ℝ) := (ENNReal.ofReal_pow (gaussianVectorExponentialTilt_nonneg h v x) 2).symm
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianVectorExponentialTilt_sq_integrable h v)
    (Eventually.of_forall fun x => sq_nonneg _), gaussianVectorExponentialTilt_integral_sq]

end
end GinibrePoincare
