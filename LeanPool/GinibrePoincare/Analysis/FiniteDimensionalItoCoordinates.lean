/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Finite dimensional Ito coordinates

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoDirectionalHessian_eq_coordinate_sum`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual real coordinate Hessian of a finite-dimensional scalar test. -/
def itoHessianEntry (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (i j : ι) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)

/-- Actual quadratic Taylor term is the sum of diagonal and cross coordinate terms. -/
theorem itoDirectionalHessian_eq_coordinate_sum (f : (ι → ℝ) → ℝ) (x h : ι → ℝ) :
    itoDirectionalHessian f x h = ∑ i, ∑ j, h i * h j * itoHessianEntry f x i j := by
  unfold itoDirectionalHessian
  rw [iteratedFDeriv_two_apply]
  have hh : h = ∑ i, h i • Pi.single i (1 : ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
    exact (Finset.univ_sum_single h).symm
  conv_lhs => rw [hh]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, itoHessianEntry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end GinibrePoincare
