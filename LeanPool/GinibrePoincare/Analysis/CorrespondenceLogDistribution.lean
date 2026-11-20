/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceLogDistribution.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceLogWeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Correspondence log distribution

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `correspondenceNegativeLog_distributional_superharmonic`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The planar Laplacian of `f`: the sum of the second real directional derivatives along `1`
and along `Complex.I`. -/
def correspondencePlanarLaplacian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I

private theorem directional_contDiff (v : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem directional_second (u v : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ f w u) z v = fderiv ℝ (fderiv ℝ f) z v u := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (∞ : ℕ∞ω)) (by simp)).differentiable (by simp) z)
    (differentiableAt_const (c := u))]
  simp

private theorem directional_dbar (v : ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    fderiv ℝ (planarDbar f) z v = (1/2 : ℂ)*
      (fderiv ℝ (fun w => fderiv ℝ f w 1) z v +
        Complex.I*fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z v) := by
  have hx := ((directional_contDiff 1 hf).differentiable (by simp) z).hasFDerivAt
  have hy := ((directional_contDiff Complex.I hf).differentiable (by simp) z).hasFDerivAt
  have h := (hx.add (hy.const_mul Complex.I)).const_mul (1/2 : ℂ)
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h.fderiv
  exact he.trans (by simp [smul_eq_mul]; ring)

theorem correspondencePlanarLaplacian_eq (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    correspondencePlanarLaplacian f z = 4*planarPartial (planarDbar f) z := by
  unfold planarPartial
  rw [directional_dbar 1 hf, directional_dbar Complex.I hf]
  have hc : fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z 1 =
      fderiv ℝ (fun w => fderiv ℝ f w 1) z Complex.I := by
    rw [directional_second _ _ hf, directional_second _ _ hf]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp [])).eq 1 Complex.I
  rw [hc]
  unfold correspondencePlanarLaplacian
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem planarDbar_contDiff (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (planarDbar f) :=
  contDiff_const.mul ((directional_contDiff 1 hf).add
    (contDiff_const.mul (directional_contDiff Complex.I hf)))

/-- Literal planar distributional identity Δ log |z| = 2π δ₀,
with the ordinary Lebesgue integral and ordinary smooth compact tests. -/
theorem correspondenceLogPotential_distributional_laplacian (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, (correspondenceLogPotential z : ℂ)*correspondencePlanarLaplacian θ z) =
      (2*Real.pi : ℂ)*θ 0 := by
  simp_rw [correspondencePlanarLaplacian_eq θ hθ]
  have he : (fun z : ℂ => (correspondenceLogPotential z : ℂ)*
      (4*planarPartial (planarDbar θ) z)) =
      (fun z : ℂ => 4*((correspondenceLogPotential z : ℂ)*planarPartial (planarDbar θ) z)) := by
    funext z
    ring
  rw [he, integral_const_mul, correspondenceLogPotential_weak_partial _
    ((planarDbar_contDiff θ hθ).of_le (by simp)) (planarDbar_compact θ hc),
    cauchyGreenKernel_fundamental_identity θ (hθ.of_le (by simp)) hc]
  ring

/-- The negative logarithm is superharmonic in the ordinary distributional sense. -/
theorem correspondenceNegativeLog_distributional_superharmonic (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (hpos : 0 ≤ (θ 0).re) :
    (∫ z : ℂ, (-(correspondenceLogPotential z : ℂ))*correspondencePlanarLaplacian θ z).re ≤ 0 := by
  simp_rw [neg_mul]
  rw [integral_neg, correspondenceLogPotential_distributional_laplacian θ hθ hc]
  norm_num [Complex.neg_re, Complex.mul_re, Complex.mul_im]
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hpos

end
end GinibrePoincare
