/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCenterProjectionEquality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreComplexProjectionGeometry
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.CenterOfMassEigenfunctions
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Center-coordinate formulas in Remark 2.8

The versioned arXiv paper is the authority for equations (2.35)--(2.40).
This module starts with the literal translation and derivative cancellation
identities used in its equality calculation.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Translation invariance along the full complex center line. -/
theorem vandermonde_add_constant (n : ℕ) (z : Configuration n) (c : ℂ) :
    vandermonde (fun k => z k + c) = vandermonde z := by
  rw [vandermonde_eq_product, vandermonde_eq_product]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  ring

/-- Equation (2.39): the holomorphic coordinate derivatives of the
Vandermonde sum to zero. -/
theorem vandermonde_sum_complex_derivatives (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, (fderiv ℂ (fun w : Configuration n => vandermonde w) z)
      (coordinateDirection j 1)) = 0 := by
  let γ : ℂ → Configuration n := fun c k => z k + c
  have hγ : HasDerivAt γ (fun _ : Fin n => (1 : ℂ)) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    exact (hasDerivAt_id (0 : ℂ)).const_add (z k)
  have hv := (differentiable_vandermonde n z).hasFDerivAt
  have hγ0 : γ 0 = z := by funext k; simp [γ]
  rw [← hγ0] at hv
  have hder := hv.comp_hasDerivAt 0 hγ
  have hfun : (fun w : Configuration n => vandermonde w) ∘ γ =
      fun _ : ℂ => vandermonde z := by
    funext c
    exact vandermonde_add_constant n z c
  rw [hfun] at hder
  have hzder := hder.unique (hasDerivAt_const (0 : ℂ) (vandermonde z))
  have hdirs : (∑ j : Fin n, coordinateDirection j 1) =
      fun _ : Fin n => (1 : ℂ) := by
    funext k
    simp [coordinateDirection]
  rw [← map_sum, hdirs]
  simpa [hγ0] using hzder

/-- Equation (2.35), as a pointwise complex identity. -/
theorem centerOfMassReal_complex_decomposition (n : ℕ) (z : Configuration n) :
    (centerOfMassReal z : ℂ) =
      (1 / 2 : ℂ) * coordinateSum z + (1 / 2 : ℂ) * conj (coordinateSum z) := by
  apply Complex.ext <;> simp [centerOfMassReal]; ring

/-- Equation (2.37): exact Vandermonde transform decomposition. -/
theorem vandermonde_centerOfMassReal_decomposition (n : ℕ) (z : Configuration n) :
    vandermonde z * (centerOfMassReal z : ℂ) =
      (1 / 2 : ℂ) * (vandermonde z * coordinateSum z) +
        (1 / 2 : ℂ) * (vandermonde z * conj (coordinateSum z)) := by
  rw [centerOfMassReal_complex_decomposition n z]
  ring

/-- Equation (2.40): the sum of first antiholomorphic creation expressions
is exactly `V * conjugate S`; the correction vanishes by equation (2.39). -/
theorem vandermonde_conjugateCenter_creation_sum (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, (conj (z j) * vandermonde z - (n : ℂ)⁻¹ *
      (fderiv ℂ (fun w : Configuration n => vandermonde w) z)
        (coordinateDirection j 1))) =
      vandermonde z * conj (coordinateSum z) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    vandermonde_sum_complex_derivatives, mul_zero, sub_zero]
  simp only [coordinateSum, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end GinibrePoincare

