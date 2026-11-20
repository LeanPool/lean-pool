/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAlgebraGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralDifferentialFactorization

/-!
# Correspondence algebra generator

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `correspondence_generator_wirtinger_display`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped BigOperators ComplexConjugate ContDiff

/-- The paper's generator at speed `α`, with the original normalization. -/
def correspondenceSpeedGenerator {n : ℕ} (α : ℝ) (f : Configuration n → ℂ)
    (z : Configuration n) : ℂ :=
  ((α / n : ℝ) : ℂ) * complexGinibrePregenerator n f z

/-- Literal real-directional display (1.29), extended componentwise to complex tests. -/
theorem correspondence_generator_real_display {n : ℕ} (α : ℝ)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    correspondenceSpeedGenerator α f z =
      ((α / n ^ 2 : ℝ) : ℂ) * ∑ j : Fin n,
        (complexSecondDirectionalDerivative f (realCoordinateDirection j) z +
          complexSecondDirectionalDerivative f (imaginaryCoordinateDirection j) z) -
      ((2 * α / n : ℝ) : ℂ) * ∑ j : Fin n,
        fderiv ℝ f z (coordinateDirection j (z j)) +
      ((2 * α / n ^ 2 : ℝ) : ℂ) * ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
        fderiv ℝ f z (coulombPairDirection j k z) := by
  unfold correspondenceSpeedGenerator
  rw [complexGinibrePregenerator_eq_direct n f (hf.differentiable (by simp))
    (fun v => (bkDirectional_contDiff v hf).differentiable (by simp))]
  unfold directComplexGinibrePregenerator
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

/-- Literal Wirtinger display (1.30) for every positive speed and smooth test. -/
theorem correspondence_generator_wirtinger_display {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 < α) (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (z : Configuration n) :
    (((n : ℝ) ^ 2 / (2 * α) : ℝ) : ℂ) * correspondenceSpeedGenerator α f z =
      2 * ∑ j : Fin n, bkPartial (dbarComponent f j) j z -
      (n : ℂ) * ∑ j : Fin n,
        (z j * bkPartial f j z + conj (z j) * dbarComponent f j z) +
      ∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
        ((bkPartial f j z - bkPartial f k z) / conj (z j - z k) +
          (dbarComponent f j z - dbarComponent f k z) / (z j - z k)) := by
  rw [correspondence_generator_real_display α f hf z]
  simp_rw [← spectral_partial_dbar_laplacian f hf,
    spectral_coordinate_derivative, spectral_coulomb_derivative]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  simp only [← Finset.mul_sum]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  field_simp
  ring

end
end GinibrePoincare

