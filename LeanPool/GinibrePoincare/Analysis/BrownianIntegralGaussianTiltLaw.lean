/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltMoments

/-!
# Brownian integral Gaussian tilt law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianReal_exponential_tilt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianPDFReal_exponential_tilt (h : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 v x*gaussianExponentialTilt h v x = gaussianPDFReal (h*(v : ℝ)) v x := by
  unfold gaussianPDFReal gaussianExponentialTilt
  rw [mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  have hv' : (v : ℝ)≠0 := by exact_mod_cast hv
  field_simp
  ring

/-- Exact Gaussian change of measure, including the degenerate zero-duration case. -/
theorem gaussianReal_exponential_tilt (h : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity (fun x => ENNReal.ofReal (gaussianExponentialTilt h v x)) =
      gaussianReal (h*(v : ℝ)) v := by
  by_cases hv : v=0
  · subst v
    simp [gaussianReal_zero_var, dirac_withDensity, gaussianExponentialTilt]
  · rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero _ hv,
      ← withDensity_mul volume (measurable_gaussianPDF 0 v)
        (show Measurable (fun x => ENNReal.ofReal (gaussianExponentialTilt h v x)) by
          unfold gaussianExponentialTilt; fun_prop)]
    congr 1
    funext x
    simp only [Pi.mul_apply, gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x),
      gaussianPDFReal_exponential_tilt h v hv x]

end
end GinibrePoincare
