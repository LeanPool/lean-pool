/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberFiniteForm.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
/-!
# Correspondence operator number finite form

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_finite_form`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
theorem correspondenceOperator_finite_hermite_inner {n : ℕ} (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    inner ℂ (finiteHermiteCombination n hn c) u=
      c.sum (fun pq a=>conj a*gaussianHermiteCoefficient hn u pq) := by
  classical
  simp [finiteHermiteCombination, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_smul_left, gaussianHermiteCoefficient_eq_inner, hermiteL2Family,
        multivariateNormalizedL2]

/-- The literal raising polynomial is the Hilbert adjoint of the ordinary
weak dbar derivative against every finite Hermite polynomial. -/
theorem correspondenceOperator_finite_raising_adjoint {n : ℕ} (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (u D : Lp ℂ 2 (complexGaussianMeasure n))
    (j : Fin n) (hu : IsGaussianWeakDbar n u D j) :
    inner ℂ (finiteHermiteCombination n hn (spectralRaisingCoefficients n j c)) u=
      inner ℂ (finiteHermiteCombination n hn c) D := by
  classical
  have he : finiteHermiteCombination n hn (spectralRaisingCoefficients n j c)=
      ∑pq ∈ c.support, ((Real.sqrt (n*(pq.2 j+1) : ℕ) : ℂ)*c pq) •
        multivariateNormalizedL2 n hn (raiseHermiteIndex j pq).1 (raiseHermiteIndex j pq).2 := by
    unfold spectralRaisingCoefficients finiteHermiteCombination
    rw [Finsupp.apply_linearCombination]
    rw [Finsupp.linearCombination_apply]
    simp only [Function.comp_apply, map_smul, Finsupp.linearCombination_single, one_smul]
    simp only [Finsupp.sum, smul_smul]
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [hermiteL2Family, multivariateNormalizedL2, mul_comm]
  rw [he, sum_inner, correspondenceOperator_finite_hermite_inner]
  simp only [Finsupp.sum, inner_smul_left, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [gaussianWeakDbar_hermiteCoefficient hn u D j hu pq,
    gaussianHermiteCoefficient_eq_inner]
  ring

/-- Actual Gaussian dbar-form integration by parts for number polynomials
against every unrestricted ordinary weak-form test. -/
theorem correspondenceOperatorNumber_finite_form {n : ℕ} (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (w : Lp ℂ 2 (complexGaussianMeasure n))
    (E : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hw : ∀ j, IsGaussianWeakDbar n w (E j) j) :
    inner ℂ (finiteGaussianNumberL2 n hn c) w=
      ∑j : Fin n, inner ℂ (finiteDbarComponentL2 n hn c j) (E j) := by
  unfold finiteGaussianNumberL2
  rw [spectralNumberCoefficients_eq_sum]
  have he : finiteHermiteCombination n hn
      (∑j : Fin n, spectralRaisingCoefficients n j (loweredCoefficients n c j))=
      ∑j : Fin n, finiteHermiteCombination n hn
        (spectralRaisingCoefficients n j (loweredCoefficients n c j)) := by
    unfold finiteHermiteCombination
    exact map_sum _ _ _
  rw [he, sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  exact correspondenceOperator_finite_raising_adjoint hn _ w (E j) j (hw j)
end
end GinibrePoincare
