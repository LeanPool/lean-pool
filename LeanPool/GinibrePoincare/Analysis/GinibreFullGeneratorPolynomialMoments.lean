/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorPolynomialMoments.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialEquilibriumOrthogonality
public import LeanPool.GinibrePoincare.Analysis.GaussianPolynomialIntegrability
public import LeanPool.GinibrePoincare.Analysis.SumRadiusCoordinates

/-!
# Ginibre full generator polynomial moments

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFull_sumRadiusPolynomial_memLp`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped ComplexConjugate BigOperators

/-- All mixed norm/radius moments needed by polynomial weak gradients are
integrable under the actual interacting Ginibre measure. -/
theorem ginibreFull_polynomial_joint_moment_integrable (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) :
    Integrable (fun z : Configuration n => ‖coordinateSum z‖ ^ a * pairwiseRadius z ^ b)
      (ginibreMeasure n) := by
  have hga : Integrable (fun s : ℂ => ‖s‖ ^ a) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure] using
      integrable_norm_pow_complexCoordinateGaussianProbability 1 a
  have hgb := Laguerre.integrable_pow_gamma (recenteredGammaShape n) b
    (recenteredGammaShape_pos n hn)
  have h := integrable_sum_radius_product n hn
    (fun s => ((‖s‖ ^ a : ℝ) : ℂ)) (fun r => ((r ^ b : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_norm.pow a))
    (Complex.continuous_ofReal.comp (continuous_id.pow b))
    (Complex.ofRealCLM.integrable_comp hga) (Complex.ofRealCLM.integrable_comp hgb)
  have hr := Complex.reCLM.integrable_comp h
  convert hr using 1
  funext z
  simp only [Complex.reCLM_apply]
  norm_cast

/-- Every monomial in the concrete sum, conjugate sum and radius is in actual
Ginibre L². -/
theorem ginibreFull_sumRadius_monomial_memLp (n : ℕ) (hn : 2 ≤ n) (a b c : ℕ) :
    MemLp (fun z : Configuration n => coordinateSum z ^ a * conj (coordinateSum z) ^ b *
      (pairwiseRadius z : ℂ) ^ c) 2 (ginibreMeasure n) := by
  have hc : Continuous (fun z : Configuration n => coordinateSum z ^ a *
      conj (coordinateSum z) ^ b * (pairwiseRadius z : ℂ) ^ c) := by
    unfold coordinateSum pairwiseRadius
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hm := ginibreFull_polynomial_joint_moment_integrable n hn (2 * a + 2 * b) (2 * c)
  convert hm using 1
  funext z
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have hR : 0 ≤ pairwiseRadius z := by
    unfold pairwiseRadius
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  rw [abs_of_nonneg hR]
  simp [pow_add, mul_comm]

/-- Actual L² membership for every polynomial in the sum/radius coordinates,
including all first and second formal derivatives. -/
theorem ginibreFull_sumRadiusPolynomial_memLp (n : ℕ) (hn : 2 ≤ n)
    (Q : MvPolynomial (Fin 3) ℂ) :
    MemLp (sumRadiusPolynomial n Q) 2 (ginibreMeasure n) := by
  rw [MvPolynomial.as_sum Q]
  have he : sumRadiusPolynomial n
      (∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d)) =
      fun z => ∑ d ∈ Q.support,
        Q.coeff d * (coordinateSum z ^ d 0 * conj (coordinateSum z) ^ d 1 *
          (pairwiseRadius z : ℂ) ^ d 2) := by
    funext z
    simp only [sumRadiusPolynomial, observablePolynomial, MvPolynomial.eval_sum,
      MvPolynomial.eval_monomial]
    congr 1
    funext d
    rw [Finsupp.prod_fintype]
    · simp [Fin.prod_univ_three, sumRadiusCoordinate, complexRadius, mul_assoc]
    · intro i
      simp
  rw [he]
  convert (memLp_finsetSum' Q.support fun d hd =>
    (ginibreFull_sumRadius_monomial_memLp n hn (d 0) (d 1) (d 2)).const_mul (Q.coeff d)) using 1
  funext z
  simp only [Finset.sum_apply]

end GinibrePoincare
