/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianFirstModeCreation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarSmoothTests

/-! # Explicit first antiholomorphic Hermite creation formula
The pointwise normalized formula is equation (2.19) of the versioned paper.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem gaussianHermite_coordinate_creation_pointwise (n : ℕ) (hn : 0 < n)
    (r s : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    (n : ℂ) * z j * multivariateNormalized n hn r s z =
      (Real.sqrt (n * s j : ℕ) : ℂ) * multivariateNormalized n hn r (lowerAt s j) z +
      (Real.sqrt (n * (r j + 1) : ℕ) : ℂ) *
        multivariateNormalized n hn (raiseAt r j) s z := by
  apply congrFun (continuous_eq_of_ae_eq_complexGaussian hn
    ((continuous_const.mul (continuous_apply j)).mul
      (contDiff_multivariateNormalized_real n hn r s).continuous)
    ((continuous_const.mul (contDiff_multivariateNormalized_real n hn r (lowerAt s
        j)).continuous).add
      (continuous_const.mul (contDiff_multivariateNormalized_real n hn (raiseAt r j) s).continuous))
    (coordinate_mul_multivariateNormalized_creation_ae n hn r s j)) z

/-- Literal equation (2.19), including the saturated lower index whose
coefficient is zero when p_j=0. -/
theorem gaussianHermite_firstMode_creation (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    multivariateNormalized n hn p (raiseAt 0 j) z =
      (Real.sqrt n : ℂ) * conj (z j) * multivariateNormalized n hn p 0 z -
      (Real.sqrt (p j) : ℂ) * multivariateNormalized n hn (lowerAt p j) 0 z := by
  have h := congrArg conj (gaussianHermite_coordinate_creation_pointwise n hn 0 p j z)
  simp only [map_add, map_mul, Complex.conj_natCast, Complex.conj_ofReal,
    conj_multivariateNormalized_swap, Pi.zero_apply, zero_add, mul_one] at h
  have hm : (Real.sqrt (n * p j : ℕ) : ℂ) =
      (Real.sqrt n : ℂ) * (Real.sqrt (p j) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), Complex.ofReal_mul]
  rw [hm] at h
  have hs : (Real.sqrt n : ℂ) * (Real.sqrt n : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    rfl
  have hne : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  apply mul_left_cancel₀ hne
  linear_combination -h - hs * (conj (z j) * multivariateNormalized n hn p 0 z)

/-- Every normalized Hermite vector belongs to precisely its
antiholomorphic-degree eigenspace. -/
theorem gaussianHermiteMode_basis (n : ℕ) (hn : 0 < n)
    (d : ℕ) (p q : Fin n → ℕ) :
    gaussianHermiteMode hn d (multivariateNormalizedL2 n hn p q) =
      if totalAntiDegree (p, q) = d then multivariateNormalizedL2 n hn p q else 0 := by
  classical
  apply (gaussianHermiteHilbertBasis n hn).repr.injective
  apply Subtype.ext
  funext rs
  change gaussianHermiteCoefficient hn (gaussianHermiteMode hn d
    (multivariateNormalizedL2 n hn p q)) rs = _
  rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode]
  have hc : gaussianHermiteCoefficient hn (multivariateNormalizedL2 n hn p q) rs =
      if rs = (p, q) then 1 else 0 := by
    rw [gaussianHermiteCoefficient, ← gaussianHermiteHilbertBasis_apply n hn (p, q),
      HilbertBasis.repr_self]
    simp [lp.single_apply, Pi.single_apply]
  rw [hc]
  by_cases ht : totalAntiDegree (p, q) = d
  · simp only [ite_eq_left ht]
    change (if totalAntiDegree rs = d then (if rs = (p, q) then 1 else 0) else 0) =
      gaussianHermiteCoefficient hn (multivariateNormalizedL2 n hn p q) rs
    rw [hc]
    by_cases he : rs = (p, q)
    · subst rs; simp [ht]
    · simp [he]
  · simp only [ite_eq_right ht, map_zero, lp.coeFn_zero, Pi.zero_apply]
    change (if totalAntiDegree rs = d then (if rs = (p, q) then (1 : ℂ) else 0) else 0) = 0
    by_cases he : rs = (p, q)
    · subst rs; simp [ht]
    · simp [he]

end
end GinibrePoincare

