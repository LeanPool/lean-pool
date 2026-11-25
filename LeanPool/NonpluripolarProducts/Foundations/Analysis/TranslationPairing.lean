/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothDistribution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth scalar pairings with translated test functions

A locally integrable density paired with a compactly supported smooth function
is smooth in the translation parameter. Differentiating the translated test
function twice gives the actual Hessian density, with two cancelling signs.
The proofs use mathlib's convolution differentiation theorem; no differentiability
of a map into the space of test functions is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ContDiff

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E)

/-- The scalar pairing with a translated function, using the sign convention
`φ(x-z)`. The theorems below prove that its defining integral exists. -/
def translationPairing (u φ : E → ℝ) (z : E) : ℝ :=
  ∫ x, u x * φ (x - z) ∂μ

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem translationPairing_eq_convolution (u φ : E → ℝ) :
    translationPairing μ u φ = u ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun x => φ (-x)) := by
  funext z
  simp only [translationPairing, convolution_def, ContinuousLinearMap.mul_apply', neg_sub]

variable {μ} [SFinite μ] [μ.IsAddLeftInvariant]

omit [NormedSpace ℝ E] [SFinite μ] [μ.IsAddLeftInvariant] in
/-- Local integrability, together with a compact continuous kernel, suffices
for integrability of every translated pairing. -/
theorem integrable_translationPairing {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : Continuous φ) (z : E) :
    Integrable (fun x => u x * φ (x - z)) μ := by
  have hs : HasCompactSupport (fun x => φ (-x)) :=
    hφs.comp_homeomorph (Homeomorph.neg E)
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.mul_apply', neg_sub] using
    hs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hu
      (hφ.comp continuous_neg) z

omit [SFinite μ] [μ.IsAddLeftInvariant] in
/-- Translation pairings inherit every finite or infinite smoothness order
of their compact kernel. The density need only be locally integrable. -/
theorem contDiff_translationPairing {u φ : E → ℝ} {n : ℕ∞}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (translationPairing μ u φ) := by
  rw [translationPairing_eq_convolution]
  exact (hφs.comp_homeomorph (Homeomorph.neg E)).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hu (hφ.comp contDiff_neg)

/-- The first derivative differentiates the translated kernel with a minus sign. -/
theorem fderiv_translationPairing {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 1 φ)
    (z v : E) :
    fderiv ℝ (translationPairing μ u φ) z v =
      -translationPairing μ u (fun x => fderiv ℝ φ x v) z := by
  let ψ : E → ℝ := fun x => φ (-x)
  have hψs : HasCompactSupport ψ := hφs.comp_homeomorph (Homeomorph.neg E)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp contDiff_neg
  have hdψ (x : E) : fderiv ℝ ψ x v = -fderiv ℝ φ (-x) v := by
    have h := (hφ.differentiable one_ne_zero (-x)).hasFDerivAt.comp x
      (hasFDerivAt_id x).neg
    simpa only [ψ, Function.comp_def, ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg] using congrArg (fun A => A v) h.fderiv
  rw [translationPairing_eq_convolution,
    (hψs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu hψ z).fderiv,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hu (hψs.fderiv ℝ)
      (hψ.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, ContinuousLinearMap.mul_apply', hdψ, neg_sub,
    mul_neg, integral_neg, translationPairing]

/-- The second derivative of the scalar pairing is the integral of the kernel's
real Hessian. The two signs from translation cancel. -/
theorem realHessian_translationPairing {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (z v w : E) :
    realHessian (translationPairing μ u φ) z v w =
      ∫ x, u x * realHessian φ (x - z) v w ∂μ := by
  have hp : ContDiff ℝ 2 (translationPairing μ u φ) :=
    contDiff_translationPairing hu hφs hφ
  rw [← fderiv_fderiv_apply_eq_realHessian hp]
  have hfirst : (fun y => fderiv ℝ (translationPairing μ u φ) y w) =
      -translationPairing μ u (fun x => fderiv ℝ φ x w) := by
    funext y
    exact fderiv_translationPairing hu hφs (hφ.of_le (by norm_num)) y w
  rw [hfirst, fderiv_neg, neg_apply,
    fderiv_translationPairing hu (hφs.fderiv_apply ℝ w)
      (contDiff_fderiv_apply_of_two hφ w), neg_neg]
  simp only [translationPairing, fderiv_fderiv_apply_eq_realHessian hφ]

omit [SFinite μ] [μ.IsAddLeftInvariant] in
/-- The second-derivative density occurring in the pairing is genuinely
integrable, because derivatives of the compact kernel retain compact support. -/
theorem integrable_translationPairing_realHessian {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (z v w : E) :
    Integrable (fun x => u x * realHessian φ (x - z) v w) μ := by
  have hs : HasCompactSupport (fun x => realHessian φ x v w) := by
    simpa only [fderiv_fderiv_apply_eq_realHessian hφ] using
      (hφs.fderiv_apply ℝ w).fderiv_apply ℝ v
  exact integrable_translationPairing hu hs (continuous_realHessian hφ v w) z

variable [NormedSpace ℂ E]

/-- The Levi form of the scalar pairing is the pairing with the classical
Levi form of its translated kernel. -/
theorem leviForm_translationPairing {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (z v : E) :
    leviForm (translationPairing μ u φ) z v =
      ∫ x, u x * leviForm φ (x - z) v ∂μ := by
  rw [leviForm, realHessian_translationPairing hu hφs hφ,
    realHessian_translationPairing hu hφs hφ,
    ← integral_add (integrable_translationPairing_realHessian hu hφs hφ z v v)
      (integrable_translationPairing_realHessian hu hφs hφ z
        (Complex.I • v) (Complex.I • v)), ← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [leviForm]; ring)

variable [IsScalarTower ℝ ℂ E]

omit [SFinite μ] [μ.IsAddLeftInvariant] in
/-- Restricting the translation parameter to a complex line gives a C²
real-valued function of the complex parameter. -/
theorem contDiff_translationPairing_complexLine {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (v : E) : ContDiff ℝ 2 (fun z : ℂ => translationPairing μ u φ (z • v)) :=
  (contDiff_translationPairing hu hφs hφ).comp (complexLineLinear v).contDiff

/-- The complex-line Laplacian of the scalar pairing is the integral of the
two corresponding real Hessian entries of the translated kernel. -/
theorem laplacian_translationPairing_complexLine {u φ : E → ℝ}
    (hu : LocallyIntegrable u μ) (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (z : ℂ) (v : E) :
    Laplacian.laplacian (fun t : ℂ => translationPairing μ u φ (t • v)) z =
      ∫ x, u x * (realHessian φ (x - z • v) v v +
        realHessian φ (x - z • v) (Complex.I • v) (Complex.I • v)) ∂μ := by
  have hp : ContDiff ℝ 2 (translationPairing μ u φ) :=
    contDiff_translationPairing hu hφs hφ
  have h := laplacian_complexLine hp (0 : E) v z
  simp only [zero_add, leviForm_translationPairing hu hφs hφ] at h
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp only [leviForm]; ring)

end SGPT.Foundations.Analysis
