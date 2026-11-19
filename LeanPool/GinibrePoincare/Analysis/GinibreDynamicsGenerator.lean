/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDynamicsGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.SumRadiusGenerator

/-! # Exact generator equations for the center and squared radius

This module records the CIR drift and carré-du-champ coefficients at the level
of the concrete Ginibre generator. It does not identify a stochastic process;
that requires an Itô formula and construction of the singular SDE.
-/

@[expose] public section

open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The paper-speed generator is the base concrete generator multiplied by
`α/n`, matching `α_n/β_n` when `β_n=n²`. -/
def ginibrePaperSpeedGenerator (n : ℕ) (α : ℝ) (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ((α / (n : ℝ) : ℝ) : ℂ) * complexGinibrePregenerator n f z

/-- The polynomial representing the squared center-of-mass norm. -/
def centerNormSqPolynomial : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- The concrete generator sends `|S|²` to its OU drift polynomial. -/
theorem sumRadiusOperator_centerNormSq (n : ℕ) :
    sumRadiusOperator n centerNormSqPolynomial =
      4 * MvPolynomial.C (1 : ℂ) - 4 * centerNormSqPolynomial := by
  simp [sumRadiusOperator, centerNormSqPolynomial, MvPolynomial.pderiv_X]
  ring

/-- The concrete generator sends the squared recentered radius to its CIR
 drift polynomial, with the paper's shape parameter. -/
theorem sumRadiusOperator_radius (n : ℕ) :
    sumRadiusOperator n (MvPolynomial.X 2) =
      4 * MvPolynomial.C (recenteredGammaShape n : ℂ) -
        4 * MvPolynomial.X 2 := by
  simp [sumRadiusOperator, MvPolynomial.pderiv_X]
  ring

/-- The second-order generator coefficient for the squared center, computed as
`L(U²) - 2 U L(U)`. -/
theorem sumRadiusOperator_centerNormSq_carreDuChamp (n : ℕ) :
    sumRadiusOperator n (centerNormSqPolynomial ^ 2) -
        2 * centerNormSqPolynomial * sumRadiusOperator n centerNormSqPolynomial =
      8 * centerNormSqPolynomial := by
  have hp (i : Fin 3) : MvPolynomial.pderiv i (2 : MvPolynomial (Fin 3) ℂ) = 0 := by
    change MvPolynomial.pderiv i (MvPolynomial.C (2 : ℂ)) = 0
    exact MvPolynomial.pderiv_C
  simp [sumRadiusOperator, centerNormSqPolynomial, MvPolynomial.pderiv_X,
    hp]
  ring

/-- The second-order generator coefficient for the centered radius, computed
as `L(R²) - 2 R L(R)`. -/
theorem sumRadiusOperator_radius_carreDuChamp (n : ℕ) :
    sumRadiusOperator n ((MvPolynomial.X 2) ^ 2) -
        2 * MvPolynomial.X 2 * sumRadiusOperator n (MvPolynomial.X 2) =
      8 * MvPolynomial.X 2 := by
  have hp (i : Fin 3) : MvPolynomial.pderiv i (2 : MvPolynomial (Fin 3) ℂ) = 0 := by
    change MvPolynomial.pderiv i (MvPolynomial.C (2 : ℂ)) = 0
    exact MvPolynomial.pderiv_C
  simp [sumRadiusOperator, MvPolynomial.pderiv_X, hp]
  ring

/-- Generator action on the observable `|S|²` for every collision-free
configuration. -/
theorem complexGinibrePregenerator_centerNormSq (n : ℕ) (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z) :
    complexGinibrePregenerator n (sumRadiusPolynomial n centerNormSqPolynomial) z =
      4 - 4 * Complex.normSq (coordinateSum z) := by
  rw [complexGinibrePregenerator_sumRadiusPolynomial n hn centerNormSqPolynomial z hz,
    sumRadiusOperator_centerNormSq]
  suffices h : coordinateSum z * conj (coordinateSum z) = (Complex.normSq (coordinateSum z) : ℂ) by
    simpa [sumRadiusPolynomial, centerNormSqPolynomial, observablePolynomial,
      sumRadiusCoordinate] using h
  calc
    coordinateSum z * conj (coordinateSum z) = conj (coordinateSum z) * coordinateSum z :=
      mul_comm _ _
    _ = (Complex.normSq (coordinateSum z) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self).symm

/-- Generator action on the squared recentered radius for every collision-free
configuration. -/
theorem complexGinibrePregenerator_radius (n : ℕ) (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z) :
    complexGinibrePregenerator n (sumRadiusPolynomial n (MvPolynomial.X 2)) z =
      4 * (recenteredGammaShape n : ℂ) - 4 * complexRadius n z := by
  rw [complexGinibrePregenerator_sumRadiusPolynomial n hn (MvPolynomial.X 2) z hz,
    sumRadiusOperator_radius]
  simp [sumRadiusPolynomial, observablePolynomial, sumRadiusCoordinate]

/-- The exact paper-speed generator drift of the squared center. -/
theorem ginibrePaperSpeedGenerator_centerNormSq (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibrePaperSpeedGenerator n α (sumRadiusPolynomial n centerNormSqPolynomial) z =
      ((4 * α / (n : ℝ) : ℝ) : ℂ) *
        (1 - (Complex.normSq (coordinateSum z) : ℂ)) := by
  rw [ginibrePaperSpeedGenerator, complexGinibrePregenerator_centerNormSq n hn z hz]
  push_cast
  ring

/-- The exact paper-speed generator drift of the centered squared radius. -/
theorem ginibrePaperSpeedGenerator_radius (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibrePaperSpeedGenerator n α (sumRadiusPolynomial n (MvPolynomial.X 2)) z =
      ((4 * α / (n : ℝ) : ℝ) : ℂ) *
        ((recenteredGammaShape n : ℂ) - complexRadius n z) := by
  rw [ginibrePaperSpeedGenerator, complexGinibrePregenerator_radius n hn z hz]
  push_cast
  ring

end
end GinibrePoincare
