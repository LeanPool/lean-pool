/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryFirstModeSeries.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliarySeriesDerivative
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicDerivative
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryEntireAnalytic
public import LeanPool.GinibrePoincare.Analysis.GaussianFirstModeCreation
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Correspondence auxiliary first mode series

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `firstModeHermite_series_real_analytic`, `firstModeHermite_series_summable`.
-/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Actual first antiholomorphic-mode reconstruction as the creation
operator on its holomorphic coefficient function. -/
theorem firstModeHermite_series_creation (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (j : Fin n) (z : Configuration n) :
    (∑' p, c p * multivariateNormalized n hn p (raiseAt 0 j) z) =
      (Real.sqrt n : ℂ) * conj (z j) *
        (∑' p, c p * multivariateNormalized n hn p 0 z) -
      (Real.sqrt n : ℂ)⁻¹ *
        fderiv ℂ (fun w => ∑' p, c p * multivariateNormalized n hn p 0 w) z
          (realCoordinateDirection j) := by
  let F : (Fin n → ℕ) → Configuration n → ℂ := fun p w =>
    c p * multivariateNormalized n hn p 0 w
  have hs := summable_holomorphicHermite_series n hn c hC z
  have hd := summable_fderiv_holomorphicHermite_series n hn c hC z
  have hfd := (hasFDerivAt_holomorphicHermite_series n hn c hC z).fderiv
  have heval := (ContinuousLinearMap.apply ℂ ℂ (realCoordinateDirection j)).map_tsum hd
  have hcoord (p : Fin n → ℕ) :
      fderiv ℂ (F p) z (realCoordinateDirection j) =
        c p * (Real.sqrt (n*p j : ℕ) : ℂ) *
          multivariateNormalized n hn (lowerAt p j) 0 z := by
    have hp : DifferentiableAt ℂ (multivariateNormalized n hn p 0) z := by
      change DifferentiableAt ℂ (fun w => multivariateNormalized n hn p 0 w) z
      simp only [multivariateNormalized_zero_right]
      fun_prop
    change fderiv ℂ (fun w => c p * multivariateNormalized n hn p 0 w) z _ = _
    rw [fderiv_const_mul hp]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_holomorphicHermite_coordinate]
    ring
  rw [hfd]
  change _ = (Real.sqrt n : ℂ) * conj (z j) * (∑' p, F p z) -
    (Real.sqrt n : ℂ)⁻¹ * ((∑' p, fderiv ℂ (F p) z) (realCoordinateDirection j))
  rw [show ((∑' p, fderiv ℂ (F p) z) (realCoordinateDirection j)) =
      ∑' p, fderiv ℂ (F p) z (realCoordinateDirection j) from heval]
  have hs1 : Summable (fun p => (Real.sqrt n : ℂ) * conj (z j) * F p z) :=
    hs.mul_left _
  have hs2 : Summable (fun p => (Real.sqrt n : ℂ)⁻¹ *
      fderiv ℂ (F p) z (realCoordinateDirection j)) :=
    (Summable.mapL (ContinuousLinearMap.apply ℂ ℂ (realCoordinateDirection j)) hd).mul_left _
  rw [← tsum_mul_left,← tsum_mul_left,← hs1.tsum_sub hs2]
  apply tsum_congr
  intro p
  rw [gaussianHermite_firstMode_creation, hcoord]
  have hroot : (Real.sqrt (n*p j : ℕ) : ℂ) =
      (Real.sqrt n : ℂ)*(Real.sqrt (p j) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), Complex.ofReal_mul]
  rw [hroot]
  have hne : (Real.sqrt n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  field_simp
  ring

theorem holomorphicHermite_series_complex_analytic (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) :
    AnalyticAt ℂ (fun w => ∑' p, c p * multivariateNormalized n hn p 0 w) z := by
  have hr := holomorphicHermiteFormalSeries_radius n c hC
  have ha := (holomorphicHermiteFormalSeries n c).analyticOnNhd z (by simp [hr])
  have he := funext (holomorphicHermiteFormalSeries_sum n hn c hC)
  rw [he] at ha
  exact ha

/-- Every actual bounded-coefficient first antiholomorphic Hermite series
is jointly real analytic, through the genuine creation formula. -/
theorem firstModeHermite_series_real_analytic (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (j : Fin n) (z : Configuration n) :
    AnalyticAt ℝ (fun w => ∑' p,
      c p * multivariateNormalized n hn p (raiseAt 0 j) w) z := by
  let F : Configuration n → ℂ := fun w => ∑' p, c p * multivariateNormalized n hn p 0 w
  have hF : AnalyticAt ℂ F z := holomorphicHermite_series_complex_analytic n hn c hC z
  have hD : AnalyticAt ℝ (fun w => fderiv ℂ F w (realCoordinateDirection j)) z := by
    have he := (ContinuousLinearMap.apply ℂ ℂ (realCoordinateDirection j)).analyticAt (fderiv ℂ F z)
    exact (he.comp hF.fderiv).restrictScalars
  have hconj : AnalyticAt ℝ (fun w : Configuration n => conj (w j)) z := by
    let L := Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj j : Configuration n →L[ℂ] ℂ).restrictScalars ℝ)
    exact L.analyticAt z
  have he : (fun w => ∑' p, c p * multivariateNormalized n hn p (raiseAt 0 j) w) =
      (fun w => (Real.sqrt n : ℂ)*conj (w j)*F w -
        (Real.sqrt n : ℂ)⁻¹*fderiv ℂ F w (realCoordinateDirection j)) :=
    funext (firstModeHermite_series_creation n hn c hC j)
  rw [he]
  exact ((analyticAt_const.mul hconj).mul hF.restrictScalars).sub
    (analyticAt_const.mul hD)

theorem firstModeHermite_term_creation (n : ℕ) (hn : 0 < n)
    (c : ℂ) (p : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    c * multivariateNormalized n hn p (raiseAt 0 j) z =
      (Real.sqrt n : ℂ)*conj (z j)*(c * multivariateNormalized n hn p 0 z) -
      (Real.sqrt n : ℂ)⁻¹ * fderiv ℂ
        (fun w => c * multivariateNormalized n hn p 0 w) z (realCoordinateDirection j) := by
  have hp : DifferentiableAt ℂ (multivariateNormalized n hn p 0) z := by
    change DifferentiableAt ℂ (fun w => multivariateNormalized n hn p 0 w) z
    simp only [multivariateNormalized_zero_right]
    fun_prop
  rw [gaussianHermite_firstMode_creation, fderiv_const_mul hp]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_holomorphicHermite_coordinate]
  have hroot : (Real.sqrt (n*p j : ℕ) : ℂ) =
      (Real.sqrt n : ℂ)*(Real.sqrt (p j) : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), Complex.ofReal_mul]
  rw [hroot]
  have hne : (Real.sqrt n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  field_simp

theorem firstModeHermite_series_summable (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (j : Fin n) (z : Configuration n) :
    Summable (fun p => c p * multivariateNormalized n hn p (raiseAt 0 j) z) := by
  have hs1 := (summable_holomorphicHermite_series n hn c hC z).mul_left
    ((Real.sqrt n : ℂ)*conj (z j))
  have hs2 := (Summable.mapL (ContinuousLinearMap.apply ℂ ℂ (realCoordinateDirection j))
    (summable_fderiv_holomorphicHermite_series n hn c hC z)).mul_left
      (Real.sqrt n : ℂ)⁻¹
  apply (hs1.sub hs2).congr
  intro p
  exact (firstModeHermite_term_creation n hn (c p) p j z).symm

end
end GinibrePoincare
