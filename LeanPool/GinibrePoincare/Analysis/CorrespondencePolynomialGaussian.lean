/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialGaussian.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityMixedPolynomial
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2Inverse
public import LeanPool.GinibrePoincare.Analysis.PolynomialChainRule
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityPolynomial
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Correspondence polynomial Gaussian

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_contDiff`,
`correspondencePolynomial_memLp_of_vandermonde`, `correspondencePolynomial_ginibre_memLp`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every arbitrary mixed polynomial lies in the actual product Gaussian L².
No permutation symmetry is imposed. -/
theorem correspondencePolynomial_gaussian_memLp (n : ℕ) (P : GinibreMixedPolynomial n) :
    MemLp (ginibreMixedPolynomialEval P) 2 (complexGaussianMeasure n) := by
  classical
  rw [MvPolynomial.as_sum P]
  have he : ginibreMixedPolynomialEval
      (∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)) =
      fun z => ∑ d ∈ P.support,
        ginibreMixedPolynomialEval (MvPolynomial.monomial d (P.coeff d)) z := by
    funext z
    simp only [ginibreMixedPolynomialEval, map_sum]
  rw [he]
  apply memLp_finsetSum
  intro d hd
  have hm : AEStronglyMeasurable
      (ginibreMixedPolynomialEval (MvPolynomial.monomial d (P.coeff d)))
      (complexGaussianMeasure n) :=
    (ginibreMixedPolynomialEval_continuous _).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (integrable_prod_norm_pow_complexGaussianMeasure n
    (fun j => 2 * (d (j, 0) + d (j, 1)))).const_mul (‖P.coeff d‖ ^ 2)
  convert hi using 1
  funext z
  simp only [ginibreMixedPolynomialEval, MvPolynomial.eval_monomial, norm_mul]
  rw [Finsupp.prod_fintype _ _ (by intro k; simp)]
  simp only [norm_prod, norm_pow]
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [ite_true, ite_eq_right h10, Complex.norm_conj]
  rw [mul_pow, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- Smoothness of arbitrary mixed polynomial evaluation over real coordinates. -/
theorem correspondencePolynomial_contDiff (n : ℕ) (P : GinibreMixedPolynomial n) :
    ContDiff ℝ ∞ (ginibreMixedPolynomialEval P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have he : ginibreMixedPolynomialEval (MvPolynomial.C c) = fun _ : Configuration n => c := by
      funext z; simp only [ginibreMixedPolynomialEval, MvPolynomial.eval_C]
    rw [he]
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration n => c))
  | add P Q hp hq =>
    have he : ginibreMixedPolynomialEval (P+Q) = ginibreMixedPolynomialEval P +
        ginibreMixedPolynomialEval Q := by
      funext z; simp only [ginibreMixedPolynomialEval, map_add, Pi.add_apply]
    rw [he]
    exact hp.add hq
  | mul_X P i hp =>
    have hi : ContDiff ℝ ∞ (fun z : Configuration n => if i.2=0 then z i.1 else conj (z i.1)) := by
      split_ifs
      · exact contDiff_apply ℝ (fun _ : Fin n => ℂ) i.1
      · exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ : Fin n => ℂ) i.1)
    have he : ginibreMixedPolynomialEval (P * MvPolynomial.X i) =
        ginibreMixedPolynomialEval P * (fun z : Configuration n => if i.2=0 then z i.1 else conj (z
            i.1)) := by
      funext z; simp only [ginibreMixedPolynomialEval, map_mul, MvPolynomial.eval_X, Pi.mul_apply]
    rw [he]
    exact hp.mul hi

/-- Any measurable representative whose Vandermonde multiple is Gaussian L²
is Ginibre L²; collision values are ignored by the actual measures. -/
theorem correspondencePolynomial_memLp_of_vandermonde {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ)
    (hL : MemLp (fun z => vandermonde z * f z) 2 (complexGaussianMeasure n)) :
    MemLp f 2 (ginibreMeasure n) := by
  have hN : MemLp (fun z => normalizedVandermondeMultiplier n z * f z) 2
      (complexGaussianMeasure n) := by
    convert hL.const_mul ((groundStateNormalization n : ℂ)⁻¹) using 1
    funext z
    unfold normalizedVandermondeMultiplier
    ring
  let u := hN.toLp (fun z => normalizedVandermondeMultiplier n z * f z)
  have hac : ginibreMeasure n ≪ complexGaussianMeasure n := by
    unfold ginibreMeasure rawGinibreMeasure
    exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  apply (inverseVandermonde_memLp (ginibreMassEvaluation n hn) u).ae_eq
  filter_upwards [hac.ae_eq hN.coeFn_toLp, hac.ae_le (vandermondeDensity_ne_zero_ae n)] with z hz hD
  have hcf : z ∉ collisionSet n := by
    intro hc
    exact hD (by simp [vandermondeDensity, (vandermondeWeight_eq_zero_iff z).mpr hc])
  unfold inverseVandermondeFunction
  rw [hz, ← mul_assoc, inverse_mul_normalizedVandermondeMultiplier (ginibreMassEvaluation n hn) hcf,
      one_mul]

/-- The Gaussian polynomial law transfers to the normalized Ginibre density
by genuine Vandermonde multiplication and its inverse L² transform. -/
theorem correspondencePolynomial_ginibre_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) :
    MemLp (ginibreMixedPolynomialEval P) 2 (ginibreMeasure n) := by
  let V : GinibreMixedPolynomial n := MvPolynomial.rename (fun j : Fin n => (j, (0 : Fin 2)))
    (polynomialVandermonde n)
  have hV (z : Configuration n) : ginibreMixedPolynomialEval V z = vandermonde z := by
    unfold ginibreMixedPolynomialEval V
    rw [MvPolynomial.eval_rename]
    change MvPolynomial.eval z (polynomialVandermonde n) = _
    exact eval_polynomialVandermonde n z
  apply correspondencePolynomial_memLp_of_vandermonde hn
  convert correspondencePolynomial_gaussian_memLp n (V * P) using 1
  funext z
  unfold ginibreMixedPolynomialEval
  rw [map_mul]
  rw [show MvPolynomial.eval (fun k => if k.2=0 then z k.1 else conj (z k.1)) V =
    vandermonde z from hV z]

end
end GinibrePoincare
