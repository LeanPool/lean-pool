/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultIBP.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultWeakLimit

/-!
# Correspondence auxiliary local Dolbeault IBP

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `localDolbeault_smooth_weak_identity`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem configurationDbar_compact_integrationByParts {n : ℕ}
    (f θ : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (j : Fin n) :
    (∫ p, f p*dbarComponent θ j p) = -(∫ p, dbarComponent f j p*θ p) := by
  have hdf (v : Configuration n) : Continuous (fun p => fderiv ℝ f p v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdθ (v : Configuration n) : Continuous (fun p => fderiv ℝ θ p v) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 (v : Configuration n) : Integrable (fun p => f p*fderiv ℝ θ p v) volume :=
    (hf.continuous.mul (hdθ v)).integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ v).mul_left)
  have hi2 (v : Configuration n) : Integrable (fun p => fderiv ℝ f p v*θ p) volume :=
    ((hdf v).mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hibp (v : Configuration n) : (∫ p, f p*fderiv ℝ θ p v) =
      -(∫ p, fderiv ℝ f p v*θ p) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi2 v) (hi1 v)
      ((hf.continuous.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun p _ => (hf.differentiable (by simp)).differentiableAt)
      (fun p _ => (hθ.differentiable (by simp)).differentiableAt)
  have hl : (∫ p, f p*dbarComponent θ j p) = (1/2 : ℂ)*
      ((∫ p, f p*fderiv ℝ θ p (realCoordinateDirection j)) +
        Complex.I*(∫ p, f p*fderiv ℝ θ p (imaginaryCoordinateDirection j))) := by
    have he : (fun p => f p*dbarComponent θ j p) = (fun p => (1/2 : ℂ)*
        (f p*fderiv ℝ θ p (realCoordinateDirection j) +
          Complex.I*(f p*fderiv ℝ θ p (imaginaryCoordinateDirection j)))) := by
      funext p
      unfold dbarComponent
      ring
    rw [he, integral_const_mul, integral_add (hi1 _) ((hi1 _).const_mul Complex.I),
        integral_const_mul]
  have hr : (∫ p, dbarComponent f j p*θ p) = (1/2 : ℂ)*
      ((∫ p, fderiv ℝ f p (realCoordinateDirection j)*θ p) +
        Complex.I*(∫ p, fderiv ℝ f p (imaginaryCoordinateDirection j)*θ p)) := by
    have he : (fun p => dbarComponent f j p*θ p) = (fun p => (1/2 : ℂ)*
        (fderiv ℝ f p (realCoordinateDirection j)*θ p +
          Complex.I*(fderiv ℝ f p (imaginaryCoordinateDirection j)*θ p))) := by
      funext p
      unfold dbarComponent
      ring
    rw [he, integral_const_mul, integral_add (hi2 _) ((hi2 _).const_mul Complex.I),
        integral_const_mul]
  rw [hl, hr, hibp, hibp]
  ring

theorem localDolbeault_smooth_weak_identity {n : ℕ}
    (U : Set (Configuration n)) (a f θ : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ U) (j : Fin n) (hsolve : ∀ p ∈ U, dbarComponent f j p = a p) :
    (∫ p, θ p*a p) = -(∫ p, dbarComponent θ j p*f p) := by
  have he (p : Configuration n) : θ p*a p = dbarComponent f j p*θ p := by
    by_cases hp : p ∈ tsupport θ
    · rw [hsolve p (hs hp), mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul, mul_zero]
  simp_rw [he]
  have hb := configurationDbar_compact_integrationByParts f θ hf hθ hc j
  have hr : (∫ p, f p*dbarComponent θ j p) = ∫ p, dbarComponent θ j p*f p := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => mul_comm _ _)
  rw [hr] at hb
  simpa only [neg_neg] using (congrArg (fun z : ℂ => -z) hb).symm

end
end GinibrePoincare
