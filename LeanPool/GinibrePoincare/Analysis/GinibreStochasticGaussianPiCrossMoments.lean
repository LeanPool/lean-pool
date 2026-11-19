/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGaussianPiCrossMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyBracket

/-! Mixed shifted moments of an actual finite product Gaussian law. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreGaussianPi_shifted_crossMoment {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (i j : ι) (hij : i ≠ j) (a b : ℝ) :
    (∫ u : ι → ℝ, (a+u i)*(b+u j) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) = a*b := by
  let ν := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have hEval (k : ι) : HasLaw (fun u : ι → ℝ => u k) (gaussianReal 0 v) ν :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) k).hasLaw
  have hMean (k : ι) (c : ℝ) : (∫ u : ι → ℝ, c+u k ∂ν) = c := by
    have h := (hEval k).integral_comp (f := fun x : ℝ => c+x) (by fun_prop)
    simp only [Function.comp_apply] at h
    rw [h]
    have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 v) := IsGaussian.integrable_id
    have he := integral_add (integrable_const c) hi
    rw [he, integral_id_gaussianReal]
    simp
  have hind : iIndepFun (fun k (u : ι → ℝ) => u k) ν := iIndepFun_pi (fun k => aemeasurable_id)
  have hi := (hind.indepFun hij).comp (show Measurable (fun x : ℝ => a+x) by fun_prop)
    (show Measurable (fun x : ℝ => b+x) by fun_prop)
  have h := hi.integral_mul_eq_mul_integral
    ((measurable_const.add (measurable_pi_apply i)).aestronglyMeasurable)
    ((measurable_const.add (measurable_pi_apply j)).aestronglyMeasurable)
  simp only [Function.comp_apply, Pi.mul_apply] at h
  rw [hMean, hMean] at h
  exact h

end
end GinibrePoincare
