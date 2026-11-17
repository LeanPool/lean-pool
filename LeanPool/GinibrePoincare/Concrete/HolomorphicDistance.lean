/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/HolomorphicDistance.lean.
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

public import LeanPool.GinibrePoincare.Concrete.NormalizedGroundState
public import LeanPool.GinibrePoincare.Concrete.SmoothTarget

/-!
# Holomorphic distance on the Ginibre side

The main proof compares the Gaussian distance to alternating holomorphic
functions with the Ginibre distance to symmetric entire functions.  The
quantities are defined here directly on representatives.
-/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- Square-integrability of a complex function for the Ginibre measure. -/
def IsGinibreL2 (n : ℕ) (h : Configuration n → ℂ) : Prop :=
  Integrable (fun z => Complex.normSq (h z)) (ginibreMeasure n)

/-- Symmetric entire square-integrable functions on the Ginibre space. -/
def IsSymmetricEntireL2 {n : ℕ}
    (h : Configuration n → ℂ) : Prop :=
  IsSymmetric h ∧ IsEntire h ∧ IsGinibreL2 n h

/-- Squared Ginibre `L²` error from a real observable to a complex function. -/
def ginibreComplexError (n : ℕ) (f : Configuration n → ℝ)
    (h : Configuration n → ℂ) : ℝ :=
  ∫ z, Complex.normSq ((f z : ℂ) - h z) ∂ginibreMeasure n

/-- Errors of symmetric entire Ginibre approximants. -/
def ginibreHolomorphicErrors (n : ℕ)
    (f : Configuration n → ℝ) : Set ℝ :=
  {r | ∃ h : Configuration n → ℂ,
    IsSymmetricEntireL2 h ∧ r = ginibreComplexError n f h}

/-- Squared distance to the symmetric entire Ginibre subspace. -/
def ginibreHolomorphicDistanceSq (n : ℕ)
    (f : Configuration n → ℝ) : ℝ :=
  sInf (ginibreHolomorphicErrors n f)

/-- Centering of a real observable. -/
def centeredObservable (n : ℕ) (f : Configuration n → ℝ) :
    Configuration n → ℝ :=
  fun z => f z - smoothGinibreMean n f

/-- Distance identity required from the isometry and holomorphic divisibility. -/
def GroundStateDistanceIdentityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      gaussianHolomorphicDistanceSq n
          (normalizedVandermondeTransform n
            (fun z => (centeredObservable n f z : ℂ))) =
        ginibreHolomorphicDistanceSq n (centeredObservable n f)

/-- Half-distance estimate supplied by the real projection geometry. -/
def GinibreHalfDistanceStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      smoothGinibreVariance n f / 2 ≤
        ginibreHolomorphicDistanceSq n (centeredObservable n f)

end

end GinibrePoincare
