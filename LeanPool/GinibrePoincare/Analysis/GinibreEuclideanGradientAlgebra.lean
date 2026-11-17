/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSmoothSobolevApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient

/-! # Product rule for the Euclidean Ginibre gradient -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped Topology ContDiff

theorem ginibreEuclideanGradient_mul {n : ℕ} (f χ : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (z : Configuration n) :
    ginibreEuclideanGradient (χ * f) z =
      χ z • ginibreEuclideanGradient f z + f z • ginibreEuclideanGradient χ z := by
  apply PiLp.ext
  intro k
  simp only [ginibreEuclideanGradient_coordinate, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
    (hf.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]

end GinibrePoincare
