/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteWeightedEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarParseval

/-!
# Hermite Weighted Energy
-/


@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GinibrePoincare

noncomputable section

open ComplexHermite


/-- Parseval written directly in terms of Hermite coefficients. -/
theorem hasSum_norm_sq_gaussianHermiteCoefficient {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) :
    HasSum (fun pq : HermiteMultiIndex n => ‖gaussianHermiteCoefficient hn g pq‖ ^ 2)
      (‖g‖ ^ 2) := by
  have hs := lp.hasSum_norm (f := (gaussianHermiteHilbertBasis n hn).repr g)
    (by norm_num)
  convert hs using 1
  · funext pq
    simp [gaussianHermiteCoefficient]
  · norm_num

/-- Raising one antiholomorphic coordinate parametrizes exactly the indices
whose corresponding coordinate is positive. -/
def raiseHermiteIndexEquivPositive {n : ℕ} (j : Fin n) :
    HermiteMultiIndex n ≃ {r : HermiteMultiIndex n // 0 < r.2 j} where
  toFun pq := ⟨raiseHermiteIndex j pq, by simp [raiseHermiteIndex, raiseAt]⟩
  invFun r := lowerHermiteIndex j r.1
  left_inv pq := by
    apply Prod.ext
    · rfl
    · funext k
      by_cases hkj : k = j
      · subst k
        simp [raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt]
      · simp [raiseHermiteIndex, lowerHermiteIndex, raiseAt, lowerAt]
  right_inv r := by
    apply Subtype.ext
    exact raiseHermiteIndex_lowerHermiteIndex j r.1 r.2

/-- The squared norm of one anti-degree mode is exactly the coefficient
mass on the corresponding fiber. -/
theorem hasSum_coefficient_norm_sq_of_totalAntiDegree {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) :
    HasSum (fun pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d} =>
      ‖gaussianHermiteCoefficient hn g pq.1‖ ^ 2)
      (‖gaussianHermiteMode hn d g‖ ^ 2) := by
  have hs := hasSum_norm_sq_gaussianHermiteCoefficient hn
    (gaussianHermiteMode hn d g)
  have hi := hs.summable.subtype (fun pq : HermiteMultiIndex n =>
    totalAntiDegree pq = d)
  have hterm (pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d}) :
      ‖gaussianHermiteCoefficient hn (gaussianHermiteMode hn d g) pq.1‖ ^ 2 =
        ‖gaussianHermiteCoefficient hn g pq.1‖ ^ 2 := by
    rw [gaussianHermiteCoefficient_eq_inner,
      inner_basis_gaussianHermiteMode hn g d pq.1, ite_eq_left pq.2]
  have htotal : (∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d},
      ‖gaussianHermiteCoefficient hn (gaussianHermiteMode hn d g) pq.1‖ ^ 2) =
      ‖gaussianHermiteMode hn d g‖ ^ 2 := by
    let f : HermiteMultiIndex n → ℝ := fun pq =>
      ‖gaussianHermiteCoefficient hn (gaussianHermiteMode hn d g) pq‖ ^ 2
    change (∑' pq : ↥({pq : HermiteMultiIndex n | totalAntiDegree pq = d} :
      Set (HermiteMultiIndex n)), f pq.1) = _
    rw [tsum_subtype {pq | totalAntiDegree pq = d} f]
    rw [← hs.tsum_eq]
    apply tsum_congr
    intro pq
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with hpq
    · rfl
    · rw [gaussianHermiteCoefficient_eq_inner,
        inner_basis_gaussianHermiteMode hn g d pq, ite_eq_right hpq]
      simp
  have hsTarget : Summable (fun pq : {pq : HermiteMultiIndex n //
      totalAntiDegree pq = d} => ‖gaussianHermiteCoefficient hn g pq.1‖ ^ 2) :=
    hi.congr (fun pq => hterm pq)
  convert hsTarget.hasSum using 1
  rw [← htotal]
  apply tsum_congr
  exact fun pq => hterm pq

/-- One coordinate of the raising identity gives the corresponding weighted
coefficient mass. -/
theorem hasSum_coordinate_weighted_gaussianHermiteCoefficient {n : ℕ}
    (hn : 0 < n) (g D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hcoeff : ∀ pq : HermiteMultiIndex n,
      gaussianHermiteCoefficient hn D pq =
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    HasSum (fun r : HermiteMultiIndex n =>
      (n * r.2 j : ℕ) * ‖gaussianHermiteCoefficient hn g r‖ ^ 2)
      (‖D‖ ^ 2) := by
  have hsD := hasSum_norm_sq_gaussianHermiteCoefficient hn D
  have hsRaise : HasSum (fun pq : HermiteMultiIndex n =>
      (n * (pq.2 j + 1) : ℕ) *
        ‖gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)‖ ^ 2)
      (‖D‖ ^ 2) := by
    apply hsD.congr_fun
    intro pq
    rw [hcoeff pq, norm_mul, mul_pow]
    have hnonneg : (0 : ℝ) ≤ n * (pq.2 j + 1) := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by exact_mod_cast hnonneg)]
  let e := raiseHermiteIndexEquivPositive j
  let f : {r : HermiteMultiIndex n // 0 < r.2 j} → ℝ := fun r =>
    (n * r.1.2 j : ℕ) * ‖gaussianHermiteCoefficient hn g r.1‖ ^ 2
  have hsSub : HasSum f (‖D‖ ^ 2) := by
    apply (e.hasSum_iff).1
    convert hsRaise using 1
    funext pq
    simp [e, f, raiseHermiteIndexEquivPositive, raiseHermiteIndex, raiseAt]
  let F : HermiteMultiIndex n → ℝ := fun r =>
    (n * r.2 j : ℕ) * ‖gaussianHermiteCoefficient hn g r‖ ^ 2
  have hsInd : Summable (({r : HermiteMultiIndex n | 0 < r.2 j} :
      Set (HermiteMultiIndex n)).indicator F) :=
    summable_subtype_iff_indicator.mp hsSub.summable
  have hFind : ({r : HermiteMultiIndex n | 0 < r.2 j} :
      Set (HermiteMultiIndex n)).indicator F = F := by
    funext r
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with hr
    · rfl
    · have hz : r.2 j = 0 := Nat.eq_zero_of_not_pos hr
      simp [F, hz]
  have hsF : Summable F := by simpa [hFind] using hsInd
  change HasSum F (‖D‖ ^ 2)
  rw [← hsSub.tsum_eq]
  convert hsF.hasSum using 1
  calc
    (∑' b, f b) =
        ∑' b : {r : HermiteMultiIndex n // 0 < r.2 j}, F b.1 := by rfl
    _ = ∑' b : HermiteMultiIndex n,
          ({r : HermiteMultiIndex n | 0 < r.2 j} : Set _).indicator F b :=
      tsum_subtype {r : HermiteMultiIndex n | 0 < r.2 j} F
    _ = ∑' b : HermiteMultiIndex n, F b := by rw [hFind]

/-- Abstract weighted Hermite-energy identity.  The only analytic input is
the displayed coordinate coefficient identity; all summation, reindexing,
and Parseval steps are discharged here. -/
theorem hasSum_weighted_gaussianHermiteMode_of_coefficient_raise {n : ℕ}
    (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ (j : Fin n) (pq : HermiteMultiIndex n),
      gaussianHermiteCoefficient hn (D j) pq =
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    HasSum (fun d : ℕ => d * ‖gaussianHermiteMode hn d g‖ ^ 2)
      ((1 / n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2) := by
  let a : HermiteMultiIndex n → ℝ := fun pq =>
    ‖gaussianHermiteCoefficient hn g pq‖ ^ 2
  have hj (j : Fin n) : HasSum (fun pq : HermiteMultiIndex n =>
      (n * pq.2 j : ℕ) * a pq) (‖D j‖ ^ 2) :=
    hasSum_coordinate_weighted_gaussianHermiteCoefficient hn g (D j) j
      (hcoeff j)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hj j)
  have hdegree : HasSum (fun pq : HermiteMultiIndex n =>
      (n : ℝ) * totalAntiDegree pq * a pq)
      (∑ j : Fin n, ‖D j‖ ^ 2) := by
    convert hsum using 1
    funext pq
    simp only [Nat.cast_mul]
    rw [totalAntiDegree, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hweighted : HasSum (fun pq : HermiteMultiIndex n =>
      totalAntiDegree pq * a pq)
      ((1 / n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2) := by
    simpa [hn0, mul_assoc] using hdegree.mul_left (1 / n : ℝ)
  let e := Equiv.sigmaFiberEquiv (@totalAntiDegree n)
  let F : (Σ d, {pq : HermiteMultiIndex n // totalAntiDegree pq = d}) → ℝ :=
    fun x => x.1 * a x.2.1
  have hsigma : HasSum F ((1 / n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2) := by
    have hc := (e.hasSum_iff).mpr hweighted
    apply hc.congr_fun
    intro x
    change (x.1 : ℝ) * a x.2.1 = totalAntiDegree x.2.1 * a x.2.1
    rw [x.2.2]
  have hFnonneg : ∀ x, 0 ≤ F x := by
    intro x
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have houter : Summable (fun d => ∑' pq :
      {pq : HermiteMultiIndex n // totalAntiDegree pq = d}, F ⟨d, pq⟩) :=
    ((summable_sigma_of_nonneg hFnonneg).mp hsigma.summable).2
  have hfiber (d : ℕ) : HasSum (fun pq :
      {pq : HermiteMultiIndex n // totalAntiDegree pq = d} => F ⟨d, pq⟩)
      (d * ‖gaussianHermiteMode hn d g‖ ^ 2) := by
    simpa [F, a] using
      (hasSum_coefficient_norm_sq_of_totalAntiDegree hn g d).mul_left (d : ℝ)
  have htarget : Summable (fun d : ℕ =>
      d * ‖gaussianHermiteMode hn d g‖ ^ 2) :=
    houter.congr (fun d => (hfiber d).tsum_eq)
  have htotal :
    (∑' d : ℕ, d * ‖gaussianHermiteMode hn d g‖ ^ 2) =
        ∑' d : ℕ, ∑' pq :
          {pq : HermiteMultiIndex n // totalAntiDegree pq = d}, F ⟨d, pq⟩ := by
      apply tsum_congr
      intro d
      exact (hfiber d).tsum_eq.symm
  rw [← hsigma.tsum_eq, hsigma.summable.tsum_sigma, ← htotal]
  exact htarget.hasSum

/-- The same weighted energy series in the positive-mode indexing used by
the deficit formula (`k` denotes anti-degree `k + 1`). -/
theorem hasSum_weighted_positiveHermiteModeMass_of_hasSum_modes {n : ℕ}
    (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n)) (E : ℝ)
    (h : HasSum (fun d : ℕ => d * ‖gaussianHermiteMode hn d g‖ ^ 2) E) :
    HasSum (fun k : ℕ => (k + 1) * positiveHermiteModeMass hn g k) E := by
  let a : ℕ → ℝ := fun d => d * ‖gaussianHermiteMode hn d g‖ ^ 2
  have htail : HasSum (fun k => a (k + 1)) E := by
    simpa [a] using (hasSum_nat_add_iff' 1).2 h
  simpa [a, positiveHermiteModeMass] using htail

/-- Positive-mode form of the abstract coordinate-derivative energy
identity. -/
theorem hasSum_weighted_positiveHermiteModeMass_of_coefficient_raise {n : ℕ}
    (hn : 0 < n) (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ (j : Fin n) (pq : HermiteMultiIndex n),
      gaussianHermiteCoefficient hn (D j) pq =
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
          gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    HasSum (fun k : ℕ => (k + 1) * positiveHermiteModeMass hn g k)
      ((1 / n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2) :=
  hasSum_weighted_positiveHermiteModeMass_of_hasSum_modes hn g _
    (hasSum_weighted_gaussianHermiteMode_of_coefficient_raise hn g D hcoeff)

/-- The full weighted Hermite energy identity for a compactly supported
smooth Gaussian function. -/
theorem hasSum_weighted_positiveHermiteModeMass_smoothCompact
    {n : ℕ} (hn : 0 < n) (F : Configuration n → ℂ)
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    HasSum (fun k : ℕ => (k + 1) *
      positiveHermiteModeMass hn (smoothCompactL2 F hF hFc) k)
      (gaussianDbarEnergy n F) := by
  have hs := hasSum_weighted_positiveHermiteModeMass_of_coefficient_raise hn
    (smoothCompactL2 F hF hFc)
    (fun j => smoothDbarComponentL2 F hF hFc j)
    (fun j pq => gaussianHermiteCoefficient_smoothDbarComponentL2_raise
      hn F hF hFc j pq)
  rw [sum_norm_sq_smoothDbarComponentL2 hn F hF hFc] at hs
  exact hs

end
end GinibrePoincare
