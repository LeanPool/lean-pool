/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSlaterEigenfunctions.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterLowering
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralNumberPolynomial
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarCompactCore
public import LeanPool.GinibrePoincare.Analysis.GinibreRadialGamma
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticHomogeneousPolynomial
public import Mathlib.Analysis.Analytic.Polynomial
/-!
# Alternative Slater eigenfunctions

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `slaterDeterminant_number_eigenfunction`,
`slater_zero_degree_homogeneous_quotient_exact`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
open ComplexHermite
noncomputable section

/-- Hermite coefficients of the normalized Slater determinant with orbital labels `pq`: the
signed sum of `Finsupp.single (slaterPermutedIndex σ pq) 1` over permutations `σ`, scaled by
`(√(slaterMultiplicity n))⁻¹`. -/
def slaterFiniteCoefficients {n : ℕ} (pq : HermiteMultiIndex n) : HermiteMultiIndex n →₀ ℂ :=
  (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ •
    ∑ σ : ParticlePermutation n, permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1

theorem slaterFiniteCoefficients_function {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n) :
    finiteHermiteFunction n hn (slaterFiniteCoefficients pq) = slaterDeterminant hn pq := by
  funext z
  rw [slaterDeterminant_signed_tensor_sum]
  simp [finiteHermiteFunction, slaterFiniteCoefficients, map_sum, Finsupp.linearCombination_single,
    smul_eq_mul]

theorem slaterFiniteCoefficients_number {n : ℕ} (pq : HermiteMultiIndex n) :
    spectralNumberCoefficients n (slaterFiniteCoefficients pq) =
      (n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq := by
  classical
  have hm (σ : ParticlePermutation n) : spectralNumberCoefficients n
      (permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1) =
      (n*totalAntiDegree pq : ℕ) • (permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1)
          := by
    simp only [spectralNumberCoefficients, map_smul, spectralDiagonalCoefficients,
      Finsupp.linearCombination_single]
    rw [slaterPermutedIndex_totalAntiDegree]
    simp [mul_comm]
  unfold slaterFiniteCoefficients
  rw [map_smul, map_sum]
  simp_rw [hm]
  rw [← Finset.smul_sum, smul_comm]

/-- Literal Section 4 (4.2) on every point, including repeated orbital labels. -/
theorem slaterDeterminant_number_eigenfunction {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (z : Configuration n) :
    (∑ j : Fin n, gaussianDbarAdjointTest j (dbarComponent (slaterDeterminant hn pq) j) z) =
      (n*totalAntiDegree pq : ℕ) * slaterDeterminant hn pq z := by
  have ha := finiteGaussianNumberL2_ae n hn (slaterFiniteCoefficients pq)
  have hb := finiteHermiteCombination_coeFn n hn
    (spectralNumberCoefficients n (slaterFiniteCoefficients pq))
  have hc : (fun z => (n*totalAntiDegree pq : ℕ)*slaterDeterminant hn pq z)
      =ᵐ[complexGaussianMeasure n]
      (fun z => ∑ j : Fin n, gaussianDbarAdjointTest j (dbarComponent (slaterDeterminant hn pq) j)
          z) := by
    filter_upwards [ha, hb] with z hza hzb
    unfold finiteGaussianNumberL2 at hza
    rw [hzb, slaterFiniteCoefficients_function] at hza
    rw [slaterFiniteCoefficients_number] at hza
    change finiteHermiteFunction n hn ((n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq) z =
        _ at hza
    have he : finiteHermiteFunction n hn ((n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq)
        =
        (n*totalAntiDegree pq : ℕ) • finiteHermiteFunction n hn (slaterFiniteCoefficients pq) := by
      exact map_nsmul (Finsupp.linearCombination ℂ _) _ _
    rw [he, slaterFiniteCoefficients_function] at hza
    simpa [smul_apply, nsmul_eq_mul] using hza
  have hs : ContDiff ℝ ∞ (slaterDeterminant hn pq) := by
    rw [← slaterFiniteCoefficients_function hn pq]
    exact contDiff_finiteHermiteFunction_smooth n hn _
  have he := continuous_eq_of_ae_eq_complexGaussian hn (contDiff_const.mul hs).continuous
    (continuous_finsetSum _ (fun j hj => (bkAdjoint_contDiff (bkDbar_contDiff hs j) j).continuous))
        hc
  exact (congrFun he z).symm

theorem slaterHolomorphicPolynomial_homogeneous (n : ℕ) (p : Fin n → ℕ) :
    (slaterHolomorphicPolynomial n p).IsHomogeneous (∑ i, p i) := by
  unfold slaterHolomorphicPolynomial
  apply MvPolynomial.IsHomogeneous.C_mul
  change (Matrix.det (Matrix.of fun i j : Fin n =>
    MvPolynomial.C (oneDimNormalization n (p i) : ℂ) * (MvPolynomial.X j) ^ p i)).IsHomogeneous _
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  apply MvPolynomial.IsHomogeneous.C_mul
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin n => MvPolynomial.C (oneDimNormalization n (p (σ i)) : ℂ)*
      MvPolynomial.X i ^ p (σ i))
    (fun i => p (σ i)) (fun i hi =>
      (MvPolynomial.isHomogeneous_X_pow i (p (σ i))).C_mul _)
  simpa only [Equiv.sum_comp σ p, Matrix.of_apply] using h

theorem slaterHolomorphicPolynomial_ne_zero {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) : slaterHolomorphicPolynomial n p ≠ 0 := by
  intro hz
  have hdist : SlaterDistinct (p, 0) := by
    intro i j hij
    exact hp (congrArg Prod.fst hij)
  have he : slaterL2 hn (p, 0) = 0 := by
    apply Lp.ext
    filter_upwards [slaterL2_ae hn (p, 0), Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hs
        h0
    rw [hs, h0,←eval_slaterHolomorphicPolynomial hn, hz]
    simp
  have hnorm := slaterL2_norm_eq_one hn (p, 0) hdist
  rw [he, norm_zero] at hnorm
  norm_num at hnorm

/-- Literal polynomial homogeneity of the quotient, with the exact degree
`sum a - n(n-1)/2` asserted in Section 4 (4.6). -/
theorem slater_zero_degree_homogeneous_quotient {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      (∀ z, slaterDeterminant hn (p, 0) z = vandermonde z*MvPolynomial.eval z Q) ∧
      Q.IsHomogeneous ((∑ i, p i)-vandermondeDegree n) ∧
      vandermondeDegree n ≤ ∑ i, p i ∧
      2*vandermondeDegree n = n*(n-1) := by
  obtain ⟨Q, hQ, hfac, hle, hscale⟩ := homogeneous_alternating_polynomial_division
    (slaterHolomorphicPolynomial_homogeneous n p)
    (slaterHolomorphicPolynomial_alternating n hn p) (slaterHolomorphicPolynomial_ne_zero hn p hp)
  have hphase : ∀ (u : ℂ) (z : Configuration n), ‖u‖=1 →
      MvPolynomial.eval (u • z) Q = u^((∑ i, p i)-vandermondeDegree n)*MvPolynomial.eval z Q := by
    intro u z hu
    have ha : (fun z : Configuration n => MvPolynomial.eval (u • z) Q) =ᵐ[complexGaussianMeasure n]
        (fun z => u^((∑ i, p i)-vandermondeDegree n)*MvPolynomial.eval z Q) := by
      filter_upwards [vandermondeDensity_ne_zero_ae n] with z hz
      apply hscale u hu z
      intro hv
      exact hz (by simp [vandermondeDensity, vandermondeWeight, hv])
    have hc1 : Continuous (fun z : Configuration n => MvPolynomial.eval (u • z) Q) :=
      (MvPolynomial.continuous_eval Q).comp (continuous_id.const_smul u)
    have hc2 : Continuous (fun z : Configuration n =>
        u^((∑ i, p i)-vandermondeDegree n)*MvPolynomial.eval z Q) :=
      continuous_const.mul (MvPolynomial.continuous_eval Q)
    have he : (fun z : Configuration n => MvPolynomial.eval (u • z) Q) =
        (fun z => u^((∑ i, p i)-vandermondeDegree n)*MvPolynomial.eval z Q) :=
      continuous_eq_of_ae_eq_complexGaussian hn hc1 hc2 ha
    exact congrFun he z
  have hA := AnalyticOnNhd.eval_mvPolynomial Q
  obtain ⟨R, hR, hEval⟩ := entire_phase_has_homogeneous_mvPolynomial
    (fun z : Configuration n => MvPolynomial.eval z Q)
    (fun z => (hA z (Set.mem_univ z)).differentiableAt)
    (hA 0 (Set.mem_univ 0)) hphase
  have hQR : Q=R := by
    apply MvPolynomial.funext
    exact hEval
  refine ⟨Q, hQ,?_, hQR.symm ▸ hR, hle, vandermondeDegree_twice n⟩
  intro z
  rw [←eval_slaterHolomorphicPolynomial hn, hfac, map_mul, eval_polynomialVandermonde]

/-- The numerical degree formula exactly as written in (4.6). -/
theorem slater_zero_degree_homogeneous_quotient_exact {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      (∀ z, slaterDeterminant hn (p, 0) z = vandermonde z*MvPolynomial.eval z Q) ∧
      Q.IsHomogeneous ((∑ i, p i)-n*(n-1)/2) := by
  obtain ⟨Q, hQ, hfac, hhom, hle, hdegree⟩ := slater_zero_degree_homogeneous_quotient hn p hp
  have hd : vandermondeDegree n = n*(n-1)/2 := by omega
  exact ⟨Q, hQ, hfac, by simpa only [hd] using hhom⟩

end
end GinibrePoincare
