/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityConjugatePolynomialDegree.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityMixedHermite
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityMixedFactor

/-!
# Ginibre Equality Conjugate Polynomial Degree
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
open scoped ComplexConjugate

/-- For a genuine holomorphic polynomial quotient, finite Gaussian conjugate
support controls its actual polynomial degree. This is the nondegenerate
Vandermonde-factor detection step, without any analytic replacement hypothesis. -/
theorem ginibreEquality_conjugate_polynomial_degree_bound {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n)) (Q : ConfigurationPolynomial n)
    (hh : (h : Configuration n → ℂ) =ᵐ[ginibreMeasure n]
      fun z => (groundStateNormalization n : ℂ) * MvPolynomial.eval z Q)
    (c : HermiteMultiIndex n →₀ ℂ) (K : ℕ)
    (hc : ∀ pq ∈ c.support, totalAntiDegree pq ≤ K)
    (hfinite : normalizedVandermondeL2 n hn (star h) = finiteHermiteCombination n hn c) :
    Q.totalDegree ≤ K := by
  let P := ginibreMixedFiniteHermitePolynomial n hn c
  have hfac : P = ginibreMixedHolomorphicLift (polynomialVandermonde n) *
      ginibreMixedAntiholomorphicLift Q := by
    apply ginibreMixedPolynomialEval_ae_injective hn
    have hh' := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
      (ginibreMassEvaluation n hn)).ae_eq hh
    have hs := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
      (ginibreMassEvaluation n hn)).ae_eq (Lp.coeFn_star h)
    have hv := normalizedVandermondeL2_coeFn_public n hn (star h)
    rw [hfinite] at hv
    have hc' := finiteHermiteCombination_coeFn n hn c
    have hN : (groundStateNormalization n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (groundStateNormalization_ne_zero_of_pos hn)
    filter_upwards [hh', hs, hv, hc'] with z hh hs hv hc'
    rw [ginibreMixedFiniteHermitePolynomial_eval]
    rw [←hc', hv, hs]
    simp only [Pi.star_apply]
    rw [hh]
    unfold ginibreMixedPolynomialEval
    rw [map_mul]
    rw [←ginibreMixedPolynomialEval, ginibreMixedHolomorphicLift_eval, eval_polynomialVandermonde,
      ←ginibreMixedPolynomialEval, ginibreMixedAntiholomorphicLift_eval]
    simp [normalizedVandermondeMultiplier, star_mul]
    field_simp
  let z : Configuration n := fun j => ((j : ℕ) : ℂ)
  have hz : MvPolynomial.eval z (polynomialVandermonde n) ≠ 0 := by
    rw [eval_polynomialVandermonde]
    exact (vandermonde_ne_zero_iff _).2 (fun i j hij => by
      exact Fin.ext (by exact_mod_cast Complex.ofReal_injective hij))
  exact ginibreEquality_mixed_factor_degree_bound_of_specialize
    (polynomialVandermonde n) Q P z hz K
    (ginibreMixedFiniteHermitePolynomial_specialize_degree n hn c K hc z) hfac

end GinibrePoincare
