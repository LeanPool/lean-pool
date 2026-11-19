/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalPiGaussianLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGaussianLaw
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Brownian orthogonal pi Gaussian law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianReal_standard_sqrt_map (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x => Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  ext
  exact Real.sq_sqrt v.property

theorem piGaussianReal_map_toLp_scaledStandard (ι : Type*) [Fintype ι] (v : ℝ≥0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map (WithLp.toLp 2) =
      scaledStandardGaussian (EuclideanSpace ℝ ι) v := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let S := fun x : ι → ℝ => fun i => Real.sqrt (v : ℝ) * x i
  have hs : μ.map S = Measure.pi (fun _ : ι => gaussianReal 0 v) := by
    rw [Measure.pi_map_pi (fun _ => (by fun_prop))]
    simp_rw [gaussianReal_standard_sqrt_map]
  unfold scaledStandardGaussian
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

end
end GinibrePoincare
