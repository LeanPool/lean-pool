/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/GaussianProbability.lean.
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

public import LeanPool.GinibrePoincare.Concrete.Configuration
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The normalized complex Gaussian probability measure

For `n` particles, each real coordinate has variance `1 / (2n)`.  We first
use Mathlib's normalized real Gaussian probability measure, take two
independent copies to obtain one complex coordinate, and then take the finite
product over the particle labels.

This construction proves the probability normalization without evaluating a
multidimensional integral.  Identification with the explicit density
`(n / π)^n exp (-n |z|²)` is deliberately kept as a separate theorem target in
`MeasureModel.lean`.
-/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- Variance of each real coordinate of the complex Gaussian reference law. -/
def realCoordinateVariance (n : ℕ) : NNReal :=
  ((2 : NNReal) * (n : NNReal))⁻¹

/-- Centered real Gaussian probability measure with variance `1 / (2n)`. -/
def realCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 (realCoordinateVariance n), by
    infer_instance⟩

/-- One complex Gaussian coordinate, assembled from two independent real
coordinates of variance `1 / (2n)`. -/
def complexCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℂ :=
  (ProbabilityMeasure.pi
      (fun _ : Fin 2 => realCoordinateGaussianProbability n)).map
    Complex.measurableEquivPi.symm

/-- Product complex Gaussian probability measure on `ℂⁿ`. -/
def complexGaussianProbability (n : ℕ) :
    ProbabilityMeasure (Configuration n) :=
  ProbabilityMeasure.pi
    (fun _ : Fin n => complexCoordinateGaussianProbability n)

/-- The Gaussian reference measure `γ_n`, viewed as an ordinary measure. -/
def complexGaussianMeasure (n : ℕ) : Measure (Configuration n) :=
  (complexGaussianProbability n : Measure (Configuration n))

instance instIsProbabilityMeasureComplexGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure
  infer_instance

/-- The Gaussian reference measure has total mass one. -/
theorem complexGaussianMeasure_univ (n : ℕ) :
    complexGaussianMeasure n Set.univ = 1 := by
  simp

/-- Named version of the Gaussian probability-measure assertion used by the
concrete development. -/
def ComplexGaussianIsProbabilityStatement : Prop :=
  ∀ n : ℕ, 0 < n → complexGaussianMeasure n Set.univ = 1

/-- The concrete Gaussian probability-measure assertion is proved. -/
theorem complexGaussianIsProbability :
    ComplexGaussianIsProbabilityStatement := by
  intro n _
  exact complexGaussianMeasure_univ n

end

end GinibrePoincare
