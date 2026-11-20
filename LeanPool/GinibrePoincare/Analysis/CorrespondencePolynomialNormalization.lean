/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondencePolynomialNormalization.lean.
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
public import LeanPool.GinibrePoincare.Analysis.KostlanProductLaw
public import Mathlib.Algebra.BigOperators.Intervals
/-!
# Correspondence polynomial normalization

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondencePolynomial_partition_constant`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Exact Gaussian-reference partition constant in the introductory footnote. -/
theorem correspondencePolynomial_partition_constant {n : ℕ} (hn : 0 < n) :
    (ginibreNormalizingMass n).toReal =
      (n.factorial : ℝ)*(∏i : Fin n, (i.val.factorial : ℝ))/(n : ℝ)^(n*(n-1)/2) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have h := ginibre_radial_expectation_transfer n hn (fun _ => 1) continuous_const
    (fun σ r => rfl) 1 (by intro r; norm_num)
  simp only [mul_one, integral_const, probReal_univ, one_smul] at h
  have hi : (∫z, kostlanWeight n z ∂complexGaussianMeasure n)=
      ∏i : Fin n, (i.val.factorial : ℝ)/(n : ℝ)^i.val := by
    unfold kostlanWeight complexGaussianMeasure complexGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_pi]
    exact (integral_fintype_prod_eq_prod (fun (i : Fin n) (z : ℂ) => Complex.normSq z^i.val)
      (μ := fun _ => (complexCoordinateGaussianProbability n : Measure ℂ))).trans
      (Finset.prod_congr rfl (fun i _ => integral_normSq_pow_coordinate n i.val hn))
  rw [hi, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum] at h
  have hs : (∑i : Fin n, i.val)=n*(n-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
    exact Finset.sum_range_id n
  rw [hs] at h
  have hm : (ginibreNormalizingMass n).toReal≠0 := ENNReal.toReal_ne_zero.mpr
    ⟨(ginibreMassEvaluation n hn).1.ne', (ginibreMassEvaluation n hn).2.ne⟩
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp [hm, hnR] at h ⊢
  nlinarith

end
end GinibrePoincare
