/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorPolynomialGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSmoothIdentification
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Ginibre full generator polynomial gradient

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFull_polynomial_projectedGradient_memLp`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped BigOperators ComplexConjugate

lemma ginibreFull_centeredScaled_norm_sq_le (n : ℕ) (z : Configuration n) (j : Fin n) :
    ‖centeredScaled z j‖ ^ 2 ≤ (n : ℝ) * pairwiseRadius z := by
  have h := congrArg Complex.re (centeredScaled_norm_sum n z)
  have he : (∑ i : Fin n, ‖centeredScaled z i‖ ^ 2) = (n : ℝ) * pairwiseRadius z := by
    simpa only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm,
      complexRadius, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_im, mul_zero, sub_zero] using h
  rw [← he]
  exact Finset.single_le_sum (fun i _ => sq_nonneg (‖centeredScaled z i‖)) (Finset.mem_univ j)

/-- Polynomial coefficients multiplied by any centered particle coordinate
have genuine interacting L² integrability. -/
theorem ginibreFull_polynomial_centered_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (j : Fin n) :
    MemLp (fun z => sumRadiusPolynomial n Q z * centeredScaled z j) 2
      (ginibreMeasure n) := by
  have hQ := ginibreFull_sumRadiusPolynomial_memLp n hn Q
  have hQR := ginibreFull_sumRadiusPolynomial_memLp n hn (Q * MvPolynomial.X 2)
  have hQRf : sumRadiusPolynomial n (Q * MvPolynomial.X 2) =
      fun z => sumRadiusPolynomial n Q z * (pairwiseRadius z : ℂ) := by
    funext z
    simp [sumRadiusPolynomial, observablePolynomial, sumRadiusCoordinate, complexRadius]
  rw [hQRf] at hQR
  have hQi := (memLp_two_iff_integrable_sq_norm hQ.aestronglyMeasurable).mp hQ
  have hQRi := (memLp_two_iff_integrable_sq_norm hQR.aestronglyMeasurable).mp hQR
  have hbound := (hQi.add hQRi).const_mul (n : ℝ)
  have hc : Continuous (fun z : Configuration n => sumRadiusPolynomial n Q z * centeredScaled z j)
      := by
    apply Continuous.mul
    · exact (differentiable_sumRadiusPolynomial n Q).continuous
    · unfold centeredScaled coordinateSum
      fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply hbound.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with z
  change ‖(‖sumRadiusPolynomial n Q z * centeredScaled z j‖ ^ 2 : ℝ)‖ ≤
    (n : ℝ) * (‖sumRadiusPolynomial n Q z‖ ^ 2 +
      ‖sumRadiusPolynomial n Q z * (pairwiseRadius z : ℂ)‖ ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [norm_mul, mul_pow, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcoord := ginibreFull_centeredScaled_norm_sq_le n z j
  have hR : pairwiseRadius z ≤ 1 + pairwiseRadius z ^ 2 := by nlinarith [sq_nonneg (pairwiseRadius z
                                                                - 1)]
  have h1 := mul_le_mul_of_nonneg_left hcoord (sq_nonneg (‖sumRadiusPolynomial n Q z‖))
  have h2 := mul_le_mul_of_nonneg_left hR
    (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (‖sumRadiusPolynomial n Q z‖)))
  nlinarith

lemma ginibreFull_polynomial_conj_centered_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (j : Fin n) :
    MemLp (fun z => sumRadiusPolynomial n Q z * conj (centeredScaled z j)) 2
      (ginibreMeasure n) := by
  apply (ginibreFull_polynomial_centered_memLp n hn Q j).congr_norm
  · have hc : Continuous (fun z : Configuration n => sumRadiusPolynomial n Q z * conj
      (centeredScaled z j)) := by
      apply Continuous.mul
      · exact (differentiable_sumRadiusPolynomial n Q).continuous
      · unfold centeredScaled coordinateSum
        fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with z
    simp only [norm_mul, Complex.norm_conj]

theorem ginibreFull_polynomial_realDirection_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (j : Fin n) :
    MemLp (fun z => fderiv ℝ (sumRadiusPolynomial n Q) z (realCoordinateDirection j))
      2 (ginibreMeasure n) := by
  have h0 := ginibreFull_sumRadiusPolynomial_memLp n hn (MvPolynomial.pderiv 0 Q)
  have h1 := ginibreFull_sumRadiusPolynomial_memLp n hn (MvPolynomial.pderiv 1 Q)
  have h2 := ginibreFull_polynomial_centered_memLp n hn (MvPolynomial.pderiv 2 Q) j
  have h3 := ginibreFull_polynomial_conj_centered_memLp n hn (MvPolynomial.pderiv 2 Q) j
  convert (h0.add h1).add (h3.add h2) using 1
  funext z
  rw [fderiv_sumRadiusPolynomial, radius_gradient_real]
  simp [coordinateSum,
    realCoordinateDirection, coordinateDirection, mul_add]

theorem ginibreFull_polynomial_imaginaryDirection_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (j : Fin n) :
    MemLp (fun z => fderiv ℝ (sumRadiusPolynomial n Q) z (imaginaryCoordinateDirection j))
      2 (ginibreMeasure n) := by
  have h0 := (ginibreFull_sumRadiusPolynomial_memLp n hn (MvPolynomial.pderiv 0 Q)).mul_const
      Complex.I
  have h1 := (ginibreFull_sumRadiusPolynomial_memLp n hn (MvPolynomial.pderiv 1 Q)).mul_const
      (-Complex.I)
  have h2 := ginibreFull_polynomial_centered_memLp n hn (MvPolynomial.pderiv 2 Q) j
  have h3 := ginibreFull_polynomial_conj_centered_memLp n hn (MvPolynomial.pderiv 2 Q) j
  convert (h0.add h1).add ((h3.sub h2).const_mul Complex.I) using 1
  funext z
  rw [fderiv_sumRadiusPolynomial, radius_gradient_imaginary]
  simp [coordinateSum,
    imaginaryCoordinateDirection, coordinateDirection]
  ring

/-- The real or imaginary Euclidean gradient of every sum/radius polynomial
belongs to actual interacting Ginibre L². -/
theorem ginibreFull_polynomial_projectedGradient_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) (T : ℂ →L[ℝ] ℝ) :
    MemLp (ginibreEuclideanGradient (fun z => T (sumRadiusPolynomial n Q z)))
      2 (ginibreMeasure n) := by
  apply memLp_piLp_iff.mpr
  intro k
  have hd : MemLp (fun z => fderiv ℝ (sumRadiusPolynomial n Q) z (ginibreCoordinateDirection k))
      2 (ginibreMeasure n) := by
    rcases k with ⟨j, k⟩
    fin_cases k
    · simpa [ginibreCoordinateDirection] using ginibreFull_polynomial_realDirection_memLp n hn Q j
    · simpa [ginibreCoordinateDirection] using ginibreFull_polynomial_imaginaryDirection_memLp n hn
        Q j
  convert T.comp_memLp' hd using 1
  funext z
  rw [ginibreEuclideanGradient_coordinate]
  have h := (T.hasFDerivAt.comp z ((differentiable_sumRadiusPolynomial n Q) z).hasFDerivAt).fderiv
  change (fderiv ℝ (T ∘ sumRadiusPolynomial n Q) z) (ginibreCoordinateDirection k) = _
  rw [h]
  rfl

end GinibrePoincare
