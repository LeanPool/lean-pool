/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltMoments.lean.
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

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw

/-!
# Brownian integral Gaussian tilt moments

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianExponentialTilt_integrable`, `gaussianExponentialTilt_integral`,
`gaussianExponentialTilt_integral_sq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The Gaussian exponential tilt `exp (h * x - h ^ 2 * v / 2)`, the density that turns the
centered Gaussian of variance `v` into the Gaussian of mean `h * v` and variance `v`. -/
def gaussianExponentialTilt (h : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (h*x-h^2*(v : ℝ)/2)

theorem gaussianExponentialTilt_integrable (h : ℝ) (v : ℝ≥0) :
    Integrable (gaussianExponentialTilt h v) (gaussianReal 0 v) := by
  have he : gaussianExponentialTilt h v =
      (fun x => Real.exp (-h^2*(v : ℝ)/2)*Real.exp (h*x)) := by
    funext x
    rw [gaussianExponentialTilt,← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrable_exp_mul_gaussianReal h).const_mul _

theorem gaussianExponentialTilt_exponential_moment (h p : ℝ) (v : ℝ≥0) :
    (∫ x, Real.exp (p*(h*x-h^2*(v : ℝ)/2)) ∂gaussianReal 0 v) =
      Real.exp ((p^2-p)*h^2*(v : ℝ)/2) := by
  have he (x : ℝ) : Real.exp (p*(h*x-h^2*(v : ℝ)/2)) =
      Real.exp (-p*h^2*(v : ℝ)/2)*Real.exp ((p*h)*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hm := mgf_gaussianReal (μ:=0) (v:=v) (p:=gaussianReal 0 v)
    (X:=fun x : ℝ => x) (by simp) (p*h)
  rw [mgf] at hm
  rw [hm,← Real.exp_add]
  congr 1
  ring

theorem gaussianExponentialTilt_integral (h : ℝ) (v : ℝ≥0) :
    (∫ x, gaussianExponentialTilt h v x ∂gaussianReal 0 v)=1 := by
  simpa [gaussianExponentialTilt] using gaussianExponentialTilt_exponential_moment h 1 v

theorem gaussianExponentialTilt_integral_sq (h : ℝ) (v : ℝ≥0) :
    (∫ x, (gaussianExponentialTilt h v x)^2 ∂gaussianReal 0 v)=Real.exp (h^2*(v : ℝ)) := by
  have he (x : ℝ) : (gaussianExponentialTilt h v x)^2 =
      Real.exp (2*(h*x-h^2*(v : ℝ)/2)) := by
    rw [gaussianExponentialTilt, pow_two,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  convert gaussianExponentialTilt_exponential_moment h 2 v using 1; congr 1; ring

end
end GinibrePoincare
