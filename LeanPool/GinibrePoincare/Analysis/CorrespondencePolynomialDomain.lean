/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialDomain.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialGeneratorL2
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorSmoothIdentification
/-!
# Correspondence polynomial domain

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_all_generator_domain`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

/-- All real projections of arbitrary mixed polynomials belong to the full
ordinary weak H¹ form and unrestricted actual generator domain. -/
theorem correspondencePolynomial_projected_H1_generator {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) :
    ∃ u v : GinibreFullValueL2 n, ∃ g : GinibreFullGradientL2 n,
      (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] (fun z => T (ginibreMixedPolynomialEval P z)) ∧
      (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        ginibrePregenerator n (fun z => T (ginibreMixedPolynomialEval P z)) ∧
      IsGinibreDistributionalGradient n u g ∧
      (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
        (correspondenceOperatorGenerator n hn).graph := by
  let f := fun z => T (ginibreMixedPolynomialEval P z)
  have hf : ContDiff ℝ ∞ f := T.contDiff.comp (correspondencePolynomial_contDiff n P)
  have hL := correspondencePolynomial_projected_memLp hn P T
  have hG := correspondencePolynomial_gradient_memLp hn P T
  have hA := correspondencePolynomial_pregenerator_memLp hn P T
  let u := hL.toLp f
  let v := hA.toLp (ginibrePregenerator n f)
  let g := hG.toLp (ginibreEuclideanGradient f)
  have hu := hL.coeFn_toLp
  have hv := hA.coeFn_toLp
  have hg := hG.coeFn_toLp
  have hw := ginibre_smooth_distributional_gradient n hn u g f hf hu hg
  exact ⟨u, v, g, hu, hv, hw, correspondenceOperatorGenerator_smooth_graph hn f hf u v g hw hu hv⟩

/-- The full differential generator on a complex-valued mixed polynomial
acts on its real and imaginary parts by the ordinary real generator. -/
def correspondencePolynomialComplexGenerator {n : ℕ} (P : GinibreMixedPolynomial n)
    (z : Configuration n) : ℂ :=
  (ginibrePregenerator n (fun y => (ginibreMixedPolynomialEval P y).re) z : ℂ) +
    Complex.I * (ginibrePregenerator n (fun y => (ginibreMixedPolynomialEval P y).im) z : ℂ)

/-- Every arbitrary polynomial in z and conjugate z belongs to the unrestricted
complex generator domain, with its actual singular differential action. This
includes nonsymmetric polynomials and the n=1 Gaussian boundary. -/
theorem correspondencePolynomial_all_generator_domain {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) :
    ∃ u v : GinibreFullComplexL2 n,
      (u : Configuration n → ℂ) =ᵐ[ginibreMeasure n] ginibreMixedPolynomialEval P ∧
      (v : Configuration n → ℂ) =ᵐ[ginibreMeasure n] correspondencePolynomialComplexGenerator P ∧
      (u, v) ∈ (correspondenceOperatorGenerator n hn).graph := by
  obtain ⟨ur, vr, gr, hur, hvr, hgr, hr⟩ := correspondencePolynomial_projected_H1_generator hn P
      Complex.reCLM
  obtain ⟨ui, vi, gi, hui, hvi, hgi, hi⟩ := correspondencePolynomial_projected_H1_generator hn P
      Complex.imCLM
  let u := ginibreFullComplexOfReal n ur + Complex.I • ginibreFullComplexOfReal n ui
  let v := ginibreFullComplexOfReal n vr + Complex.I • ginibreFullComplexOfReal n vi
  refine ⟨u, v,?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_add (ginibreFullComplexOfReal n ur) (Complex.I •
      ginibreFullComplexOfReal n ui),
      Lp.coeFn_smul Complex.I (ginibreFullComplexOfReal n ui),
      ginibreFullComplexOfReal_ae n ur, ginibreFullComplexOfReal_ae n ui, hur, hui] with z ha hs hr
          hi hR hI
    dsimp only [u]
    rw [ha, Pi.add_apply, hs, Pi.smul_apply, hr, hi, hR, hI]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    rw [mul_comm Complex.I]
    exact Complex.re_add_im _
  · filter_upwards [Lp.coeFn_add (ginibreFullComplexOfReal n vr) (Complex.I •
      ginibreFullComplexOfReal n vi),
      Lp.coeFn_smul Complex.I (ginibreFullComplexOfReal n vi),
      ginibreFullComplexOfReal_ae n vr, ginibreFullComplexOfReal_ae n vi, hvr, hvi] with z ha hs hr
          hi hR hI
    dsimp only [v]
    rw [ha, Pi.add_apply, hs, Pi.smul_apply, hr, hi, hR, hI]
    rfl
  · exact (correspondenceOperatorGenerator n hn).graph.add_mem hr
      ((correspondenceOperatorGenerator n hn).graph.smul_mem Complex.I hi)

end
end GinibrePoincare
