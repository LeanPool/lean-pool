/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberSecondBounds.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaPolynomial
/-!
# Correspondence operator number second bounds

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorFiniteSecond_dist_le`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- On finitely supported Hermite coefficients, the `L²` combination of the coefficients lowered
in coordinate `j` and then in coordinate `k`. -/
def correspondenceOperatorFiniteSecond (n : ℕ) (hn : 0 < n) (j k : Fin n) :
    (HermiteMultiIndex n→₀ℂ)→ₗ[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (Finsupp.linearCombination ℂ (hermiteL2Family n hn)).comp
    ((spectralLoweringCoefficients n k).comp (spectralLoweringCoefficients n j))
theorem correspondenceOperatorFiniteSecond_eq (n : ℕ) (hn : 0 < n)
    (j k : Fin n) (c : HermiteMultiIndex n →₀ ℂ) :
    correspondenceOperatorFiniteSecond n hn j k c=
      finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k) := by
  simp [correspondenceOperatorFiniteSecond, spectralLoweringCoefficients_eq,
      finiteHermiteCombination]

/-- On finitely supported Hermite coefficients, the `L²` combination of the number-operator
coefficients `spectralNumberCoefficients n`. -/
def correspondenceOperatorFiniteNumber (n : ℕ) (hn : 0 < n) :
    (HermiteMultiIndex n→₀ℂ)→ₗ[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (Finsupp.linearCombination ℂ (hermiteL2Family n hn)).comp (spectralNumberCoefficients n)

theorem correspondenceOperatorFiniteSecond_norm_le (n : ℕ) (hn : 0 < n)
    (j k : Fin n) (c : HermiteMultiIndex n →₀ ℂ) :
    ‖correspondenceOperatorFiniteSecond n hn j k c‖≤‖finiteGaussianNumberL2 n hn c‖ := by
  rw [correspondenceOperatorFiniteSecond_eq]
  have hBK := bkFinite_integrated_identity n hn c
  have h1 : ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k)‖^2≤
      ∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j)
          l)‖^2 :=
    Finset.single_le_sum (fun l _=>sq_nonneg ‖finiteHermiteCombination n hn (loweredCoefficients n
        (loweredCoefficients n c j) l)‖) (Finset.mem_univ k)
  have h2 : (∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients
      n c j) l)‖^2)≤
      ∑i : Fin n,∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n
          (loweredCoefficients n c i) l)‖^2 :=
    Finset.single_le_sum (fun i _=>Finset.sum_nonneg (s := Finset.univ) (fun l _=>
      sq_nonneg ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c i)
          l)‖)) (Finset.mem_univ j)
  have hp : 0≤(n : ℝ)*(∑j : Fin n, ‖finiteDbarComponentL2 n hn c j‖^2) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _=>sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

theorem correspondenceOperatorFiniteSecond_dist_le (n : ℕ) (hn : 0 < n)
    (j k : Fin n) (c d : HermiteMultiIndex n →₀ ℂ) :
    dist (correspondenceOperatorFiniteSecond n hn j k c) (correspondenceOperatorFiniteSecond n hn j
        k d)≤
      dist (finiteGaussianNumberL2 n hn c) (finiteGaussianNumberL2 n hn d) := by
  rw [dist_eq_norm, dist_eq_norm,← map_sub]
  have he : finiteGaussianNumberL2 n hn c-finiteGaussianNumberL2 n hn d=
      finiteGaussianNumberL2 n hn (c-d) := by
    change correspondenceOperatorFiniteNumber n hn c-correspondenceOperatorFiniteNumber n hn d=
      correspondenceOperatorFiniteNumber n hn (c-d)
    rw [map_sub]
  rw [he]
  exact correspondenceOperatorFiniteSecond_norm_le n hn j k (c-d)
end
end GinibrePoincare
