/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGaussianFourthMoment.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRMoments

/-! # Genuine Gaussian fourth moments for Brownian quadratic-increment estimates -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreGaussian_centered_fourthMoment (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v : ℝ)^2 := by
  have hMom := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 4
  change iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 = (∫ x : ℝ, x^4 ∂gaussianReal 0
      v) at hMom
  rw [mgf_fun_id_gaussianReal] at hMom
  simp only [zero_mul, zero_add] at hMom
  rw [← hMom]
  let g := fun t : ℝ => Real.exp ((v : ℝ)*t^2/2)
  have hExp (t : ℝ) : HasDerivAt g ((v : ℝ)*t*g t) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    dsimp [g]
    ring
  have h1 : deriv g = fun t => (v : ℝ)*t*g t := funext (fun t => (hExp t).deriv)
  have h2 : deriv (fun t => (v : ℝ)*t*g t) = fun t => ((v : ℝ)+(v : ℝ)^2*t^2)*g t := by
    funext t
    have h := (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hExp t)).deriv
    convert! h using 1; dsimp only [id_eq, Pi.pow_apply]; ring
  have h3 : deriv (fun t => ((v : ℝ)+(v : ℝ)^2*t^2)*g t) =
      fun t => (3*(v : ℝ)^2*t+(v : ℝ)^3*t^3)*g t := by
    funext t
    have h := (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ)^2)).const_add (v : ℝ)).mul (hExp
        t)).deriv
    convert! h using 1; dsimp only [id_eq, Pi.pow_apply]; ring
  have h4 : deriv (fun t => (3*(v : ℝ)^2*t+(v : ℝ)^3*t^3)*g t) 0 = 3*(v : ℝ)^2 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (3*(v : ℝ)^2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ)^3))).mul (hExp 0)).deriv
    convert! h using 1; simp [g]
  change iteratedDeriv 4 g 0 = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2, h3, h4]

end
end GinibrePoincare
