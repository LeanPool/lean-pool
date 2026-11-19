/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltVectorCentering.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorLaw

/-!
# Brownian integral Gaussian tilt vector centering

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianVectorExponentialTilt_centered_lintegral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- True centered-innovation formula for every nonnegative measurable test. -/
theorem gaussianVectorExponentialTilt_centered_lintegral {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (gaussianVectorExponentialTilt h v x)*
      f (fun i => x i-h i*(v : ℝ)) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  classical
  let Q := (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
    (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x))
  have hmap := gaussianReal_pi_exponential_tilt_centered h v
  have hm : Measurable (fun x : ι→ℝ => fun i => x i-h i*(v : ℝ)) := by fun_prop
  have hh := lintegral_map (μ:=Q) hf hm
  change (∫⁻ x, f x ∂Q.map (fun x i => x i-h i*(v : ℝ))) = _ at hh
  rw [hmap] at hh
  have hfm : Measurable (fun x : ι→ℝ => f (fun i => x i-h i*(v : ℝ))) := by fun_prop
  dsimp only [Q] at hh
  rw [lintegral_withDensity_eq_lintegral_mul _ (by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop) hfm] at hh
  exact hh.symm

end
end GinibrePoincare
