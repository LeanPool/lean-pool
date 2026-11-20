/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberFormDomain.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberForm
/-! # Exact first-energy form domain

Parseval for each coordinate weak derivative gives a weighted coefficient sum.
Summing over coordinates combines those weights into `n * totalAntiDegree`,
which is the first-energy weight (not its square, used for the operator domain).

Conversely, raise the coefficient index in each coordinate. The coordinate
weight is bounded by the total-degree weight, so first-energy summability gives
the coefficient criterion for every ordinary weak derivative. Choosing those
coordinate derivatives establishes the full form-domain equivalence.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
theorem correspondenceOperatorNumber_ordinary_form_hasSum {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    HasSum (fun pq : HermiteMultiIndex n=>
      ((n*totalAntiDegree pq : ℕ) : ℝ)*‖gaussianHermiteCoefficient hn u pq‖^2)
      (∑j : Fin n, ‖D j‖^2) := by
  have hsum := hasSum_sum (s := Finset.univ) (fun j _=>
    hasSum_coordinate_weighted_gaussianHermiteCoefficient hn u (D j) j
      (gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j)))
  convert hsum using 1
  funext pq
  simp only [totalAntiDegree, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]

/-- The exact ordinary Gaussian form domain is the spectral first-energy
summability domain, with no derivative completion hypothesis. -/
theorem correspondenceOperatorNumber_ordinary_form_domain_iff {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∃D : Fin n→Lp ℂ 2 (complexGaussianMeasure n),∀j, IsGaussianWeakDbar n u (D j) j) ↔
      Summable (fun pq : HermiteMultiIndex n=>
        ((n*totalAntiDegree pq : ℕ) : ℝ)*‖gaussianHermiteCoefficient hn u pq‖^2) := by
  constructor
  · rintro ⟨D, hD⟩
    exact (correspondenceOperatorNumber_ordinary_form_hasSum hn u D hD).summable
  · intro hs
    have hex (j : Fin n) : ∃D, IsGaussianWeakDbar n u D j := by
      apply (gaussianWeakDbar_exists_iff_summable hn u j).mpr
      have hshift := hs.comp_injective (raiseHermiteIndex_injective j)
      apply Summable.of_nonneg_of_le (fun _=>sq_nonneg _) _ hshift
      intro pq
      change ‖(Real.sqrt (n*(pq.2 j+1) : ℕ) : ℂ)*gaussianHermiteCoefficient hn u (raiseHermiteIndex
          j pq)‖^2≤
        ((n*totalAntiDegree (raiseHermiteIndex j pq) : ℕ) : ℝ)*
          ‖gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)‖^2
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      norm_cast
      apply Nat.mul_le_mul_left
      have h := Finset.single_le_sum (fun i _=>Nat.zero_le ((raiseHermiteIndex j pq).2 i))
        (Finset.mem_univ j)
      simpa [raiseHermiteIndex, raiseAt, totalAntiDegree] using h
    choose D hD using hex
    exact ⟨D, hD⟩
end
end GinibrePoincare
