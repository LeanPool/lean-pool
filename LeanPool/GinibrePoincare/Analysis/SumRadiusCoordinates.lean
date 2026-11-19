/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/SumRadiusCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadiusGradient

/-!
# Sum radius coordinates

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `fderiv_sumRadiusCoordinate_one`, `fderiv_sumRadiusCoordinate_two`,
`second_sumRadiusCoordinate_two`, `differentiable_sumRadiusPolynomial_direction`.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The three complex polynomial coordinates `S`, `conj S`, and the real radius. -/
def sumRadiusCoordinate (n : ℕ) : Fin 3 → Configuration n → ℂ :=
  ![coordinateSum, (fun z => conj (coordinateSum z)), complexRadius n]

@[simp] theorem fderiv_coordinateSum (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (coordinateSum : Configuration n → ℂ) z v = coordinateSum v := by
  have he : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by funext w; simp
  rw [he, ContinuousLinearMap.fderiv]

@[simp] theorem fderiv_conjugate_coordinateSum (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (fun w : Configuration n => conj (coordinateSum w)) z v = conj (coordinateSum v) := by
  have he : (fun w : Configuration n => conj (coordinateSum w)) =
      Complex.conjCLE.toContinuousLinearMap.comp (coordinateSumCLM n) := by funext w; simp
  rw [he, ContinuousLinearMap.fderiv]
  simp

theorem differentiable_sumRadiusCoordinate (n : ℕ) (i : Fin 3) :
    Differentiable ℝ (sumRadiusCoordinate n i) := by
  fin_cases i
  · change Differentiable ℝ coordinateSum
    have he : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by funext w; simp
    rw [he]; fun_prop
  · change Differentiable ℝ (fun w : Configuration n => conj (coordinateSum w))
    have he : (fun w : Configuration n => conj (coordinateSum w)) =
        Complex.conjCLE.toContinuousLinearMap.comp (coordinateSumCLM n) := by funext w; simp
    rw [he]; fun_prop
  · exact differentiable_complexRadius n

theorem differentiable_sumRadiusCoordinate_direction (n : ℕ) (i : Fin 3) (v : Configuration n) :
    Differentiable ℝ (fun z => fderiv ℝ (sumRadiusCoordinate n i) z v) := by
  fin_cases i
  · change Differentiable ℝ (fun z => fderiv ℝ (coordinateSum : Configuration n → ℂ) z v)
    simp only [fderiv_coordinateSum]; fun_prop
  · change Differentiable ℝ (fun z => fderiv ℝ (fun w : Configuration n => conj (coordinateSum w)) z
      v)
    simp only [fderiv_conjugate_coordinateSum]; fun_prop
  · change Differentiable ℝ (fun z => fderiv ℝ (complexRadius n) z v)
    rw [radius_directional_eq]; fun_prop

@[simp] theorem second_sumRadiusCoordinate_zero (n : ℕ) (v z : Configuration n) :
    complexSecondDirectionalDerivative (sumRadiusCoordinate n 0) v z = 0 := by
  simp [complexSecondDirectionalDerivative, sumRadiusCoordinate]

@[simp] theorem second_sumRadiusCoordinate_one (n : ℕ) (v z : Configuration n) :
    complexSecondDirectionalDerivative (sumRadiusCoordinate n 1) v z = 0 := by
  simp [complexSecondDirectionalDerivative, sumRadiusCoordinate]

@[simp] theorem fderiv_sumRadiusCoordinate_zero (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (sumRadiusCoordinate n 0) z v = coordinateSum v :=
  fderiv_coordinateSum n z v

@[simp] theorem fderiv_sumRadiusCoordinate_one (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (sumRadiusCoordinate n 1) z v = conj (coordinateSum v) :=
  fderiv_conjugate_coordinateSum n z v

@[simp] theorem fderiv_sumRadiusCoordinate_two (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (sumRadiusCoordinate n 2) z v = fderiv ℝ (complexRadius n) z v := rfl

@[simp] theorem second_sumRadiusCoordinate_two (n : ℕ) (v z : Configuration n) :
    complexSecondDirectionalDerivative (sumRadiusCoordinate n 2) v z = 2 * complexRadius n v :=
  second_complexRadius n v z

/-- Evaluation of a polynomial in the actual sum and radius coordinates. -/
def sumRadiusPolynomial (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) : Configuration n → ℂ :=
  observablePolynomial (sumRadiusCoordinate n) Q

theorem differentiable_sumRadiusPolynomial (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) :
    Differentiable ℝ (sumRadiusPolynomial n Q) :=
  differentiable_observablePolynomial _ (differentiable_sumRadiusCoordinate n) Q

/-- First derivative of an arbitrary polynomial in `S`, `conj S`, and `R`. -/
theorem fderiv_sumRadiusPolynomial (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ) (z v : Configuration n) :
    fderiv ℝ (sumRadiusPolynomial n Q) z v =
      sumRadiusPolynomial n (MvPolynomial.pderiv 0 Q) z * coordinateSum v +
      sumRadiusPolynomial n (MvPolynomial.pderiv 1 Q) z * conj (coordinateSum v) +
      sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z * fderiv ℝ (complexRadius n) z v := by
  rw [sumRadiusPolynomial, fderiv_observablePolynomial _ (differentiable_sumRadiusCoordinate n)]
  simp [Fin.sum_univ_three, sumRadiusCoordinate, sumRadiusPolynomial, add_assoc]

/-- Polynomial directional derivatives are differentiable, so the concrete complex generator
applies. -/
theorem differentiable_sumRadiusPolynomial_direction (n : ℕ) (Q : MvPolynomial (Fin 3) ℂ)
    (v : Configuration n) : Differentiable ℝ (fun z => fderiv ℝ (sumRadiusPolynomial n Q) z v) := by
  have he : (fun z => fderiv ℝ (sumRadiusPolynomial n Q) z v) = fun z =>
      sumRadiusPolynomial n (MvPolynomial.pderiv 0 Q) z * coordinateSum v +
      sumRadiusPolynomial n (MvPolynomial.pderiv 1 Q) z * conj (coordinateSum v) +
      sumRadiusPolynomial n (MvPolynomial.pderiv 2 Q) z * fderiv ℝ (complexRadius n) z v := by
    funext z; exact fderiv_sumRadiusPolynomial n Q z v
  rw [he]
  exact ((differentiable_sumRadiusPolynomial n _).mul_const _ |>.add
    ((differentiable_sumRadiusPolynomial n _).mul_const _)).add
      ((differentiable_sumRadiusPolynomial n _).mul (differentiable_sumRadiusCoordinate_direction n
          2 v))

end
end GinibrePoincare
