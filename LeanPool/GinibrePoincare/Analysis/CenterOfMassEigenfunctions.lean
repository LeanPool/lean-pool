/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CenterOfMassEigenfunctions.lean.
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

public import LeanPool.GinibrePoincare.Concrete.Generator

/-!
# Center Of Mass Eigenfunctions
-/


@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Real-linear continuous sum of all particle coordinates. -/
def coordinateSumCLM (n : ℕ) : Configuration n →L[ℝ] ℂ :=
  ∑ j : Fin n, ContinuousLinearMap.proj j

@[simp] theorem coordinateSumCLM_apply (n : ℕ) (z : Configuration n) :
    coordinateSumCLM n z = coordinateSum z := by
  simp [coordinateSumCLM, coordinateSum]

@[simp] theorem coordinateSum_coordinateDirection {n : ℕ} (j : Fin n) (w : ℂ) :
    coordinateSum (coordinateDirection j w) = w := by
  simp [coordinateSum, coordinateDirection]

@[simp] theorem coordinateSum_coulombPairDirection {n : ℕ} (j k : Fin n) (z : Configuration n) :
    coordinateSum (coulombPairDirection j k z) = 0 := by
  rw [coulombPairDirection, ← coordinateSumCLM_apply, map_sub]
  simp

/-- Any real-linear statistic annihilating the pair drift has eigenvalue two. -/
theorem ginibrePregenerator_linear (n : ℕ) (T : Configuration n →L[ℝ] ℝ)
    (hT : ∀ (j k : Fin n) (z : Configuration n), T (coulombPairDirection j k z) = 0)
    (z : Configuration n) :
    ginibrePregenerator n T z = -2 * T z := by
  have hsecond (v : Configuration n) : secondDirectionalDerivative T v z = 0 := by
    simp [secondDirectionalDerivative, T.fderiv]
  have hsum : (∑ j : Fin n, coordinateDirection j (z j)) = z := by
    funext k
    simp [coordinateDirection]
  simp only [ginibrePregenerator, T.fderiv, hT, hsecond, configurationLaplacian,
    Finset.sum_const_zero, mul_zero, zero_sub, add_zero]
  rw [← map_sum, hsum]
  ring

/-- The concrete generator sends the real sum coordinate to minus twice itself. -/
theorem ginibrePregenerator_centerOfMassReal (n : ℕ) (z : Configuration n) :
    ginibrePregenerator n centerOfMassReal z = -2 * centerOfMassReal z := by
  let T := Complex.reCLM.comp (coordinateSumCLM n)
  have h := ginibrePregenerator_linear n T (by
    intro j k w
    simp [T]) z
  have heq : (T : Configuration n → ℝ) = centerOfMassReal := by
    funext w; simp [T, centerOfMassReal]
  simpa only [heq] using h

/-- The concrete generator sends the imaginary sum coordinate to minus twice itself. -/
theorem ginibrePregenerator_centerOfMassImag (n : ℕ) (z : Configuration n) :
    ginibrePregenerator n centerOfMassImag z = -2 * centerOfMassImag z := by
  let T := Complex.imCLM.comp (coordinateSumCLM n)
  have h := ginibrePregenerator_linear n T (by
    intro j k w
    simp [T]) z
  have heq : (T : Configuration n → ℝ) = centerOfMassImag := by
    funext w; simp [T, centerOfMassImag]
  simpa only [heq] using h

/-- Complex extension of the existing real concrete pregenerator. -/
def complexGinibrePregenerator (n : ℕ) (f : Configuration n → ℂ) (z : Configuration n) : ℂ :=
  (ginibrePregenerator n (fun w => (f w).re) z : ℂ) +
    Complex.I * (ginibrePregenerator n (fun w => (f w).im) z : ℂ)

/-- The genuine concrete generator equation for the first complex sum polynomial. -/
theorem complexGinibrePregenerator_coordinateSum (n : ℕ) (z : Configuration n) :
    complexGinibrePregenerator n coordinateSum z = -2 * coordinateSum z := by
  unfold complexGinibrePregenerator
  change (ginibrePregenerator n centerOfMassReal z : ℂ) +
    Complex.I * (ginibrePregenerator n centerOfMassImag z : ℂ) = _
  rw [ginibrePregenerator_centerOfMassReal, ginibrePregenerator_centerOfMassImag]
  apply Complex.ext <;> simp [centerOfMassReal, centerOfMassImag]

end
end GinibrePoincare
