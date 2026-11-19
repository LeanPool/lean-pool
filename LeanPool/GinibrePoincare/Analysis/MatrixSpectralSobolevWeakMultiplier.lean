/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevWeakMultiplier.lean.
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

public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification
public import LeanPool.GinibrePoincare.Concrete.Configuration
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Actual ordinary weak product rule for matrix Sobolev truncations -/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem local_integrable_mul_compact_test (m : ℕ) (f θ : Configuration m → ℝ)
    (hf : LocallyIntegrable f volume) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    Integrable (fun x => f x * θ x) volume := by
  simpa only [smul_eq_mul, mul_comm] using hf.integrable_smul_left_of_hasCompactSupport hθ hc

/-- Ordinary distributional directional derivatives satisfy the genuine smooth
compact multiplier rule on the entire configuration space. -/
theorem configuration_weak_directional_derivative_mul (m : ℕ)
    (f g χ : Configuration m → ℝ) (v : Configuration m)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hχ : ContDiff ℝ ∞ χ)
    (hw : ∀ θ : Configuration m → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x * θ x) = -(∫ x, f x * fderiv ℝ θ x v)) :
    ∀ θ : Configuration m → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, (χ x * g x + f x * fderiv ℝ χ x v) * θ x) =
        -(∫ x, (χ x * f x) * fderiv ℝ θ x v) := by
  intro θ hθ hc
  have he := hw (χ * θ) (hχ.mul hθ) hc.mul_left
  have hd (x : Configuration m) :
      fderiv ℝ (χ * θ) x v = χ x * fderiv ℝ θ x v + θ x * fderiv ℝ χ x v := by
    rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
      (hθ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hgi := local_integrable_mul_compact_test m g (χ * θ) hg (hχ.mul hθ).continuous hc.mul_left
  simp only [Pi.mul_apply] at hgi
  simp only [Pi.mul_apply] at he
  have hfi := local_integrable_mul_compact_test m f
    (fun x => fderiv ℝ χ x v * θ x) hf
    (((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hθ.continuous)
    hc.mul_left
  have hfj := local_integrable_mul_compact_test m f
    (fun x => χ x * fderiv ℝ θ x v) hf
    (hχ.continuous.mul ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const))
    (hc.fderiv_apply ℝ v).mul_left
  have hl : (∫ x, (χ x * g x + f x * fderiv ℝ χ x v) * θ x) =
      (∫ x, g x * (χ x * θ x)) + (∫ x, f x * (fderiv ℝ χ x v * θ x)) := by
    rw [← integral_add hgi hfi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp; ring
  have hr : (∫ x, f x * fderiv ℝ (χ * θ) x v) =
      (∫ x, f x * (χ x * fderiv ℝ θ x v)) + (∫ x, f x * (fderiv ℝ χ x v * θ x)) := by
    rw [← integral_add hfj hfi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp; rw [hd]; ring
  rw [hr] at he
  rw [hl]
  have ht : (∫ x, (χ x * f x) * fderiv ℝ θ x v) =
      (∫ x, f x * (χ x * fderiv ℝ θ x v)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [ht]
  linarith

end
end GinibrePoincare
