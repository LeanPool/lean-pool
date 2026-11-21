/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2Mollification

/-! # Quantitative actual mollification from a derived L² translation modulus

This extends the preceding C¹ argument to measurable actual L² inputs.
The hypothesis is a genuine translation estimate, not an approximation or
compactness assumption. Normalized smooth kernels have bounded density,
which proves all pointwise Jensen integrability conditions.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual smoothing L² membership follows from the proved translation-modulus
error bound, without assuming an approximation property. -/
theorem bumpMollification_memLp_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    MemLp (bumpMollification φ f) 2 volume := by
  have he := (bumpMollification_integral_error_of_translation_bound φ hfm hf C htrans).1
  convert he.add hf using 1
  funext x
  simp

/-- The actual L² distance between smoothing and input is controlled by the
derived translation modulus. This is the uniform-approximation input for Ascoli. -/
theorem bumpMollification_L2_dist_le_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    ‖(bumpMollification_memLp_of_translation_bound φ hfm hf C htrans).toLp (bumpMollification φ
      f) -
      hf.toLp f‖ ≤ φ.rOut * C := by
  have hnorm : ‖(bumpMollification_memLp_of_translation_bound φ hfm hf C htrans).toLp
    (bumpMollification φ f) -
      hf.toLp f‖ ^ 2 = ∫ x, (bumpMollification φ f x - f x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      ((bumpMollification_memLp_of_translation_bound φ hfm hf C htrans).toLp (bumpMollification
        φ f))
      (hf.toLp f), (bumpMollification_memLp_of_translation_bound φ hfm hf C htrans).coeFn_toLp,
      hf.coeFn_toLp] with x hsub hsm hf'
    rw [hsub, Pi.sub_apply, hsm, hf', Real.inner_apply, pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg φ.rOut_pos.le hC)).mp
  rw [hnorm, mul_pow]
  exact (bumpMollification_integral_error_of_translation_bound φ hfm hf C htrans).2

/-- Common compact support of inputs gives common enlarged compact support
of the actual smoothing family. -/
theorem bumpMollification_eq_zero_off_add_support (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : Set E} (hsupp : ∀ x ∉ K, f x = 0)
    (x : E) (hx : x ∉ Metric.closedBall (0 : E) φ.rOut + K) :
    bumpMollification φ f x = 0 := by
  by_contra hne
  have hs : x ∈ Function.support (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) := hne
  have hsub := support_convolution_subset (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (f := φ.normed volume) (g := f) (μ := (volume : Measure E))
  obtain ⟨y, hy, z, hz, hyz⟩ := hsub hs
  apply hx
  refine ⟨y, ?_, z, ?_, hyz⟩
  · have hy' : y ∈ tsupport (φ.normed volume) := subset_tsupport _ hy
    rwa [φ.tsupport_normed_eq] at hy'
  · by_contra hzK
    exact hz (hsupp z hzK)

end CutoffRigidity
