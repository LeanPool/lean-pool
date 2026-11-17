/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Concrete/MeasureModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The canonical real-density interfaces are moved from
GinibrePoincare/Analysis/GinibreIntegrationByParts.lean.
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

public import LeanPool.GinibrePoincare.Concrete.Weights
public import LeanPool.GinibrePoincare.Concrete.GaussianProbability

/-!
# Concrete Gaussian density and Ginibre measure

The Gaussian reference measure `complexGaussianMeasure n` is constructed in
`GaussianProbability.lean` as a genuine finite product probability measure.
This file also defines the explicit density measure

`(n / π)^n exp (-n |z|²) dz`.

Equality of these two descriptions is stated explicitly as
`ComplexGaussianDensityIdentificationStatement`; it is not hidden in a
definition.  The unnormalised Ginibre measure is then `|V_n|² γ_n`, and its
actual total mass is used for normalization.
-/


@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- Canonical Lebesgue/Haar volume on the finite-dimensional real space `ℂⁿ`. -/
def configurationVolume (n : ℕ) : Measure (Configuration n) :=
  volume

/-- Explicit density of the normalized complex Gaussian reference measure. -/
def complexGaussianDensity (n : ℕ) (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((n : ℝ) / Real.pi) ^ n) * gaussianWeight n z)

/-- Measure defined directly by the explicit Gaussian density. -/
def complexGaussianDensityMeasure (n : ℕ) : Measure (Configuration n) :=
  (configurationVolume n).withDensity (complexGaussianDensity n)

/-- Identification of the product Gaussian law with its explicit Lebesgue
density. This proposition is proved as `complexGaussianDensityIdentification`
in `Analysis/ComplexGaussianDensity.lean`; it is defined separately here to
keep the measure construction independent of its density proof. -/
def ComplexGaussianDensityIdentificationStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    complexGaussianMeasure n = complexGaussianDensityMeasure n

/-- Once the density identification is available, normalization of the
explicit density follows from the already proved probability normalization. -/
theorem complexGaussianDensityMeasure_univ_of_identification
    (h : ComplexGaussianDensityIdentificationStatement)
    (n : ℕ) (hn : 0 < n) :
    complexGaussianDensityMeasure n Set.univ = 1 := by
  rw [← h n hn]
  exact complexGaussianMeasure_univ n

/-- Vandermonde density as an extended nonnegative real. -/
def vandermondeDensity {n : ℕ} (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z)

/-- The ordinary real density whose `ENNReal.ofReal` is the product of the
Vandermonde and explicit complex-Gaussian densities. -/
def ginibreLebesgueDensityReal (n : ℕ) (z : Configuration n) : ℝ :=
  (((n : ℝ) / Real.pi) ^ n) * vandermondeWeight z * gaussianWeight n z

/-- The real Ginibre Lebesgue density is nonnegative. -/
theorem ginibreLebesgueDensityReal_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreLebesgueDensityReal n z := by
  unfold ginibreLebesgueDensityReal
  exact mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg n)
    Real.pi_pos.le) _) (vandermondeWeight_nonneg z)) (gaussianWeight_nonneg n z)

/-- The two extended nonnegative density factors multiply to the `ofReal`
of the ordinary real density. -/
theorem vandermondeDensity_mul_complexGaussianDensity (n : ℕ)
    (z : Configuration n) :
    vandermondeDensity z * complexGaussianDensity n z =
      ENNReal.ofReal (ginibreLebesgueDensityReal n z) := by
  unfold vandermondeDensity complexGaussianDensity ginibreLebesgueDensityReal
  rw [← ENNReal.ofReal_mul (vandermondeWeight_nonneg z)]
  congr 1
  ring

/-- The unnormalised measure `|V_n|² γ_n`. -/
def rawGinibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity vandermondeDensity

/-- Actual total mass of the unnormalised Ginibre measure. -/
def ginibreNormalizingMass (n : ℕ) : ℝ≥0∞ :=
  rawGinibreMeasure n Set.univ

/-- The normalized Ginibre measure `μ_n`. -/
def ginibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (ginibreNormalizingMass n)⁻¹ • rawGinibreMeasure n

/-- Positivity and finiteness of the actual normalizing mass. -/
def GinibreMassIsValid (n : ℕ) : Prop :=
  0 < ginibreNormalizingMass n ∧ ginibreNormalizingMass n < ⊤

/-- Positive finite Ginibre normalizing mass for the Ginibre gas. -/
def GinibreMassEvaluationStatement : Prop :=
  ∀ n : ℕ, 0 < n → GinibreMassIsValid n

/-- Exact probability-measure statement for the normalized Ginibre law. -/
def GinibreMeasureIsProbabilityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    ginibreMeasure n Set.univ = 1

/-- Normalizing by a positive finite raw mass produces total mass one. -/
theorem ginibreMeasure_univ_of_mass_valid (n : ℕ)
    (h : GinibreMassIsValid n) :
    ginibreMeasure n Set.univ = 1 := by
  rcases h with ⟨hpos, htop⟩
  simp only [ginibreMeasure, Measure.smul_apply, ginibreNormalizingMass]
  exact ENNReal.inv_mul_cancel hpos.ne' htop.ne

/-- A positive finite raw mass equips the normalized Ginibre measure with the
usual probability-measure typeclass. -/
theorem ginibreMeasure_isProbabilityMeasure_of_mass_valid (n : ℕ)
    (h : GinibreMassIsValid n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ⟨ginibreMeasure_univ_of_mass_valid n h⟩

/-- The mass-validity theorem implies the probability-measure theorem. -/
theorem ginibreMeasureIsProbability_of_mass_evaluation
    (h : GinibreMassEvaluationStatement) :
    GinibreMeasureIsProbabilityStatement := by
  intro n hn
  exact ginibreMeasure_univ_of_mass_valid n (h n hn)

/-- Mass evaluation supplies the probability typeclass at every positive
particle number. -/
theorem ginibreMeasure_isProbabilityMeasure_of_mass_evaluation
    (h : GinibreMassEvaluationStatement) (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ginibreMeasure_isProbabilityMeasure_of_mass_valid n (h n hn)

end

end GinibrePoincare
