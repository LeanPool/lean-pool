/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultMollification.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultIteration
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Correspondence auxiliary local Dolbeault mollification

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `ordinaryDolbeaultMollify_contDiff`, `ordinaryDolbeaultMollify_closed_on`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

/-- The convolution `φ ⋆ U` of complex functions on configurations with respect to Lebesgue
measure. -/
def ordinaryDolbeaultMollify {n : ℕ} (φ U : Configuration n → ℂ) : Configuration n → ℂ :=
  φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] U

theorem ordinaryDolbeaultMollify_contDiff {n : ℕ} (φ U : Configuration n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hu : LocallyIntegrable U volume) :
    ContDiff ℝ ∞ (ordinaryDolbeaultMollify φ U) :=
  hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hφ hu

theorem ordinaryDolbeaultMollify_directional {n : ℕ} (φ U : Configuration n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hu : LocallyIntegrable U volume)
    (x v : Configuration n) :
    fderiv ℝ (ordinaryDolbeaultMollify φ U) x v =
      ∫ y, fderiv ℝ φ (x-y) v * U y := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (hφ.of_le (by simp)) hu x
  rw [show ordinaryDolbeaultMollify φ U =
    φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] U from rfl, hd.fderiv, convolution_eq_swap]
  have hi := ((hc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℂ).precompL (Configuration n))
      (hφ.continuous_fderiv (by simp)) hu x).integrable_swap
  rw [ContinuousLinearMap.integral_apply hi v]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.mul_apply']

theorem ordinaryDolbeaultMollify_dbar {n : ℕ} (φ U : Configuration n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hu : LocallyIntegrable U volume)
    (x : Configuration n) (j : Fin n) :
    dbarComponent (ordinaryDolbeaultMollify φ U) j x =
      ∫ y, dbarComponent φ j (x-y) * U y := by
  have hi (v : Configuration n) : Integrable (fun y => fderiv ℝ φ (x-y) v * U y) volume := by
    have hdc : HasCompactSupport (fun y => fderiv ℝ φ (x-y) v) :=
      (hc.fderiv_apply ℝ v).comp_homeomorph (Homeomorph.subLeft x)
    have hd : Continuous (fun y => fderiv ℝ φ (x-y) v) :=
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    simpa only [smul_eq_mul] using hu.integrable_smul_left_of_hasCompactSupport hd hdc
  simp only [dbarComponent, ordinaryDolbeaultMollify_directional φ U hφ hc hu]
  have he : (fun y => (1/2 : ℂ)*(fderiv ℝ φ (x-y) (realCoordinateDirection j) +
      Complex.I*fderiv ℝ φ (x-y) (imaginaryCoordinateDirection j)) * U y) =
      (fun y => (1/2 : ℂ)*(fderiv ℝ φ (x-y) (realCoordinateDirection j) * U y +
        Complex.I*(fderiv ℝ φ (x-y) (imaginaryCoordinateDirection j)*U y))) := by
    funext y
    ring
  rw [he, integral_const_mul, integral_add (hi _) ((hi _).const_mul Complex.I), integral_const_mul]

/-- Ordinary distributional closedness passes to the actual smooth
convolution at every point whose translated kernel support stays in Ω. -/
theorem ordinaryDolbeaultMollify_closed_on {n : ℕ}
    (Ω : Set (Configuration n)) (α : Fin n → Configuration n → ℂ)
    (hα : ∀ j, LocallyIntegrable (α j) volume)
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ω → ∀ j k,
        (∫ y, dbarComponent θ k y * α j y) = ∫ y, dbarComponent θ j y * α k y)
    (φ : Configuration n → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Configuration n) (hx : tsupport (fun y => φ (x-y)) ⊆ Ω) (j k : Fin n) :
    dbarComponent (ordinaryDolbeaultMollify φ (α j)) k x =
      dbarComponent (ordinaryDolbeaultMollify φ (α k)) j x := by
  let θ : Configuration n → ℂ := fun y => φ (x-y)
  have hθ : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y : Configuration n) : fderiv ℝ θ y = -fderiv ℝ φ (x-y) := by
    have hh := (hφ.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [show θ = φ ∘ (fun y : Configuration n => x-y) from rfl, hh.fderiv]
    ext v
    simp
  have hdb (l : Fin n) (y : Configuration n) :
      dbarComponent θ l y = -dbarComponent φ l (x-y) := by
    simp only [dbarComponent, hd, neg_apply]
    ring
  have he := hclosed θ hθ hcθ hx j k
  simp_rw [hdb, neg_mul, integral_neg] at he
  rw [ordinaryDolbeaultMollify_dbar φ (α j) hφ hc (hα j),
    ordinaryDolbeaultMollify_dbar φ (α k) hφ hc (hα k)]
  exact neg_injective he

end
end GinibrePoincare
