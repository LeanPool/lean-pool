/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorHermiteMultiplier.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupCFC
/-!
# Correspondence operator Hermite multiplier

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorHermiteMultiplier_isSelfAdjoint`.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- Bounded real spectral multipliers on the genuine Gaussian Hermite basis. -/
def correspondenceOperatorHermiteMultiplierCoefficients {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) : lp (fun _ : HermiteMultiIndex n=>ℂ) 2 :=
  ⟨fun pq=>(w pq : ℂ)*gaussianHermiteCoefficient hn u pq,
    (lp.memℓp ((gaussianHermiteHilbertBasis n hn).repr u)).mono' (by
      intro pq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw pq))⟩

/-- The `L²` vector whose Gaussian Hermite coefficients are `w pq` times those of `u`. -/
def correspondenceOperatorHermiteMultiplierValue {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) : Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm
    (correspondenceOperatorHermiteMultiplierCoefficients hn w hw u)

@[simp] theorem correspondenceOperatorHermiteMultiplier_coefficient {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (correspondenceOperatorHermiteMultiplierValue hn w hw u) pq=
      (w pq : ℂ)*gaussianHermiteCoefficient hn u pq := by
  simp [gaussianHermiteCoefficient, correspondenceOperatorHermiteMultiplierValue,
    correspondenceOperatorHermiteMultiplierCoefficients]

theorem correspondenceOperatorHermiteMultiplier_norm_le {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖correspondenceOperatorHermiteMultiplierValue hn w hw u‖≤‖u‖ := by
  rw [correspondenceOperatorHermiteMultiplierValue, LinearIsometryEquiv.norm_map,
    ← (gaussianHermiteHilbertBasis n hn).repr.norm_map u]
  apply lp.norm_mono (by norm_num)
  intro pq
  change ‖(w pq : ℂ)*gaussianHermiteCoefficient hn u pq‖≤‖gaussianHermiteCoefficient hn u pq‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw pq)

/-- The Gaussian Hermite multiplier with real weights `|w pq| ≤ 1`, as a bounded operator on
`L²(complexGaussianMeasure n)`. -/
def correspondenceOperatorHermiteMultiplier {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1) :
    Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  LinearMap.mkContinuous
    { toFun := correspondenceOperatorHermiteMultiplierValue hn w hw
      map_add' := by
        intro u v
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (x y : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (x+y) pq =
              gaussianHermiteCoefficient hn x pq+gaussianHermiteCoefficient hn y pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right]
        rw [correspondenceOperatorHermiteMultiplier_coefficient, ha, ha,
          correspondenceOperatorHermiteMultiplier_coefficient,
          correspondenceOperatorHermiteMultiplier_coefficient, mul_add]
      map_smul' := by
        intro a u
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (x : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (a • x) pq =a*gaussianHermiteCoefficient hn x pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right]
        change gaussianHermiteCoefficient hn (correspondenceOperatorHermiteMultiplierValue hn w hw
            (a • u)) pq =
          gaussianHermiteCoefficient hn (a • correspondenceOperatorHermiteMultiplierValue hn w hw u)
              pq
        rw [correspondenceOperatorHermiteMultiplier_coefficient, ha, ha,
          correspondenceOperatorHermiteMultiplier_coefficient]
        ring }
    1 (by intro u; simpa using correspondenceOperatorHermiteMultiplier_norm_le hn w hw u)

theorem correspondenceOperatorHermiteMultiplier_isSelfAdjoint {n : ℕ} (hn : 0 < n)
    (w : HermiteMultiIndex n → ℝ) (hw : ∀ pq, |w pq| ≤ 1) :
    IsSelfAdjoint (correspondenceOperatorHermiteMultiplier hn w hw) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  rw [← (gaussianHermiteHilbertBasis n hn).repr.inner_map_map,
    ← (gaussianHermiteHilbertBasis n hn).repr.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro pq
  change inner ℂ (gaussianHermiteCoefficient hn
      (correspondenceOperatorHermiteMultiplierValue hn w hw u) pq)
      (gaussianHermiteCoefficient hn v pq)=
    inner ℂ (gaussianHermiteCoefficient hn u pq)
      (gaussianHermiteCoefficient hn (correspondenceOperatorHermiteMultiplierValue hn w hw v) pq)
  rw [correspondenceOperatorHermiteMultiplier_coefficient,
    correspondenceOperatorHermiteMultiplier_coefficient]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring
end
end GinibrePoincare
