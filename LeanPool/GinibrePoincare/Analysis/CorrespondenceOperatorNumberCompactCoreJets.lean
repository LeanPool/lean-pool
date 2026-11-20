/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCompactCoreJets.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactGraph
public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaPolynomial
public import LeanPool.GinibrePoincare.Analysis.CorrespondencePolynomialGaussian
/-!
# Correspondence operator number compact core jets

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceNumber_double_coordinate_memLp`,
`correspondenceNumber_secondCutoff_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
open ComplexHermite
noncomputable section

theorem correspondenceNumber_hermite_polynomial (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) : ∃P : GinibreMixedPolynomial n, ginibreMixedPolynomialEval
        P=multivariateNormalized n hn p q := by
  refine ⟨∏i : Fin n, MvPolynomial.C ((oneDimNormalization n (p i)*oneDimNormalization n (q i) : ℝ)
      : ℂ)*
    ∑k∈Finset.range (min (p i) (q i)+1),
      MvPolynomial.C (((-((n : ℝ)⁻¹ : ℂ))^k)*(k.factorial : ℂ)*(Nat.choose (p i) k : ℂ)*(Nat.choose
          (q i) k : ℂ))*
        MvPolynomial.X (i, 0)^(p i-k)*MvPolynomial.X (i, 1)^(q i-k),?_⟩
  funext z
  simp [ginibreMixedPolynomialEval, multivariateNormalized, normalizedEval_eq_sum]

theorem correspondenceNumber_finite_polynomial (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) : ∃P : GinibreMixedPolynomial n, ginibreMixedPolynomialEval
        P=finiteHermiteFunction n hn c := by
  classical
  choose P hP using fun pq : HermiteMultiIndex n=>correspondenceNumber_hermite_polynomial n hn pq.1
      pq.2
  refine ⟨∑pq∈c.support, MvPolynomial.C (c pq)*P pq,?_⟩
  funext z
  simp only [ginibreMixedPolynomialEval, map_sum, map_mul, MvPolynomial.eval_C]
  change (∑pq∈c.support, c pq*ginibreMixedPolynomialEval (P pq) z)=_
  simp only [hP, finiteHermiteFunction, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem correspondenceNumber_double_coordinate_memLp (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j k : Fin n) :
    MemLp (fun z =>z k*z j*finiteHermiteFunction n hn c z) 2 (complexGaussianMeasure n) := by
  obtain ⟨P, hP⟩ := correspondenceNumber_finite_polynomial n hn c
  have h := correspondencePolynomial_gaussian_memLp n (MvPolynomial.X (k, 0)*MvPolynomial.X (j,
      0)*P)
  have he : ginibreMixedPolynomialEval (MvPolynomial.X (k, 0)*MvPolynomial.X (j, 0)*P)=
      (fun z=>z k*z j*finiteHermiteFunction n hn c z) := by
    funext z
    simp only [ginibreMixedPolynomialEval, map_mul, MvPolynomial.eval_X, ite_true]
    rw [← hP]
    rfl
  rwa [he] at h

theorem correspondenceNumber_secondCutoff_memLp {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) (m : ℕ) :
    MemLp (fun z=>((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ)*f z)
      2 (complexGaussianMeasure n) := by
  obtain ⟨M, hM0, hM⟩ := bkCutoff_second_derivative_bound
  have hc : Continuous (deriv (deriv (sobolevCutoff m))) :=
    ((show ContDiff ℝ ((∞:ℕ∞ω)+1) (sobolevCutoff m) by simpa using sobolevCutoff_smooth
                                                         m).deriv').continuous_deriv (by simp)
  apply hf.of_le_mul (c:=M) ((Complex.continuous_ofReal.comp (hc.comp
      contDiff_configurationNormSq.continuous)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α:=ℝ) m; nlinarith))

theorem correspondenceNumber_secondCutoff_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) :
    Tendsto (fun m=>(correspondenceNumber_secondCutoff_memLp f hf m).toLp
      (fun z=>((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ)*f z)) atTop (𝓝 0)
          := by
  obtain ⟨M, hM0, hM⟩ := bkCutoff_second_derivative_bound
  have hz : MemLp (fun _ : Configuration n=>(0 : ℂ)) 2 (complexGaussianMeasure n) := MemLp.zero'
  have hi : Integrable (fun z=>(M*‖f z‖)^2) (complexGaussianMeasure n) := by
    simpa only [mul_pow] using ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp
        hf).const_mul (M^2)
  have ht := gaussianL2_toLp_tendsto_of_dominated_error _ _
    (correspondenceNumber_secondCutoff_memLp f hf) hz (fun z=>M*‖f z‖) hi
    (fun m z=>by
      rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hM m _).trans (div_le_self hM0 (by
          have := Nat.cast_nonneg (α:=ℝ) m; nlinarith))) (norm_nonneg _))
    (fun z=>by simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp
                 (bkCutoff_second_derivative_tendsto (configurationNormSq z))).mul_const (f z))
  simpa using ht

end
end GinibrePoincare
