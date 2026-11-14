/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.InnerProductSpace.Laplacian
/-!
# Second derivatives of compactly supported convolutions

Smooth compactly supported kernels regularize continuous functions.

The Hessian of a convolution is the convolution of the kernel Hessian.
-/
public section
open MeasureTheory ContinuousLinearMap
open scoped Convolution
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [SFinite μ] [μ.IsAddLeftInvariant]
  {w b : E → ℝ}

omit [SFinite μ] [μ.IsAddLeftInvariant] [FiniteDimensional ℝ E] in
/-- Smooth compactly supported kernels regularize continuous functions. -/
theorem contDiff_convolution_of_continuous {n : ℕ∞}
    (hw : Continuous w) (hb : ContDiff ℝ n b) (hbc : HasCompactSupport b) :
    ContDiff ℝ n (w ⋆[lsmul ℝ ℝ, μ] b) :=
  hbc.contDiff_convolution_right (lsmul ℝ ℝ) hw.locallyIntegrable hb

omit [FiniteDimensional ℝ E] in
/-- The Hessian of a convolution is the convolution of the kernel Hessian. -/
theorem fderiv_fderiv_convolution (hw : Continuous w) (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (x u v : E) :
    fderiv ℝ (fderiv ℝ (w ⋆[lsmul ℝ ℝ, μ] b)) x u v =
      ∫ z, w z * (fderiv ℝ (fderiv ℝ b) (x - z) u v) ∂μ := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hb₁ : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hdb : ContDiff ℝ 1 (fderiv ℝ b) := hb.fderiv_right (by norm_num)
  have hd : fderiv ℝ (w ⋆[L, μ] b) = w ⋆[L.precompR E, μ] fderiv ℝ b := by
    funext y
    exact (hbc.hasFDerivAt_convolution_right L hw.locallyIntegrable hb₁ y).fderiv
  rw [hd, (hbc.fderiv ℝ).hasFDerivAt_convolution_right (L.precompR E)
    hw.locallyIntegrable hdb x |>.fderiv]
  rw [convolution_precompR_apply _ hw.locallyIntegrable (hbc.fderiv ℝ |>.fderiv ℝ)
    (hdb.continuous_fderiv one_ne_zero)]
  have hc : HasCompactSupport (fun z => fderiv ℝ (fderiv ℝ b) z u) :=
    (hbc.fderiv ℝ |>.fderiv ℝ).comp_left
      (g := ContinuousLinearMap.apply ℝ _ u) (map_zero (ContinuousLinearMap.apply ℝ _ u))
  have hh : Continuous (fun z => fderiv ℝ (fderiv ℝ b) z u) :=
    (hdb.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [convolution_precompR_apply _ hw.locallyIntegrable hc hh]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Scalar evaluations of the kernel Hessian have compact support. -/
theorem hasCompactSupport_kernel_hessian (hbc : HasCompactSupport b) (u v : E) :
    HasCompactSupport (fun z => fderiv ℝ (fderiv ℝ b) z u v) := by
  let ev₁ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ _ u
  let ev₂ : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ _ v
  exact (hbc.fderiv ℝ |>.fderiv ℝ).comp_left
    (g := ev₂.comp ev₁) (map_zero (ev₂.comp ev₁))

omit [FiniteDimensional ℝ E] [SFinite μ] [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [MeasurableSpace E] [BorelSpace E] in
/-- Scalar evaluations of a `C²` kernel Hessian are continuous. -/
theorem continuous_kernel_hessian (hb : ContDiff ℝ 2 b) (u v : E) :
    Continuous (fun z => fderiv ℝ (fderiv ℝ b) z u v) := by
  let ev₁ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ _ u
  let ev₂ : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ _ v
  have hdb : ContDiff ℝ 1 (fderiv ℝ b) := hb.fderiv_right (by norm_num)
  exact (ev₂.comp ev₁).continuous.comp (hdb.continuous_fderiv one_ne_zero)

omit [FiniteDimensional ℝ E] [SFinite μ] [μ.IsAddLeftInvariant] in
/-- Scalar Hessian evaluations against a continuous function are integrable. -/
theorem integrable_mul_kernel_hessian (hw : Continuous w) (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (x u v : E) :
    Integrable (fun z => w z * fderiv ℝ (fderiv ℝ b) (x - z) u v) μ :=
  (hasCompactSupport_kernel_hessian hbc u v).convolutionExists_right (lsmul ℝ ℝ)
    hw.locallyIntegrable (continuous_kernel_hessian hb u v) x

open InnerProductSpace Laplacian
/-- The Laplacian commutes with convolution by a compactly supported `C²` kernel. -/
theorem laplacian_convolution (hw : Continuous w) (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (x : E) :
    Δ (w ⋆[lsmul ℝ ℝ, μ] b) x = ∫ z, w z * Δ b (x - z) ∂μ := by
  classical
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis b, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [fderiv_fderiv_convolution hw hb hbc, Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact integrable_mul_kernel_hessian hw hb hbc x _ _
end LiebThirring
end
