/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TranslationPairing
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smooth approximate identities with controlled support

The kernels are actual normalized smooth bump functions. Their supports shrink
at a fixed inner/outer radius ratio, so Lebesgue differentiation gives almost
everywhere convergence for locally integrable densities. No monotonicity in
the radius is claimed: the chosen bump base need not be radial.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Convolution

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive scale determines smooth bumps whose outer radii tend to zero
and whose inner radii are exactly half their outer radii. -/
def shrinkingBump (R : ℝ) (hR : 0 < R) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (R / ((n : ℝ) + 1)) / 2
  rOut := R / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

omit [NormedSpace ℝ E] in
theorem shrinkingBump_rOut_le (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (shrinkingBump (E := E) R hR n).rOut ≤ R := by
  change R / ((n : ℝ) + 1) ≤ R
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

omit [NormedSpace ℝ E] in
theorem shrinkingBump_radius_ratio (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (shrinkingBump (E := E) R hR n).rOut =
      2 * (shrinkingBump (E := E) R hR n).rIn := by
  dsimp [shrinkingBump]
  ring

omit [NormedSpace ℝ E] in
theorem tendsto_shrinkingBump_rOut (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => (shrinkingBump (E := E) R hR n).rOut) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  simpa only [shrinkingBump, div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul h : Tendsto (fun n : ℕ => R * ((n : ℝ) + 1)⁻¹) atTop (𝓝 (R * 0)))

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Smooth averaging against a nonnegative normalized kernel. -/
def mollify (u : E → ℝ) (φ : ContDiffBump (0 : E)) : E → ℝ :=
  translationPairing μ u (φ.normed μ)

/-- The translation-pairing convention agrees with the usual convolution:
the normalized bump centered at zero is even. -/
theorem mollify_eq_convolution (u : E → ℝ) (φ : ContDiffBump (0 : E)) :
    mollify μ u φ = φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := by
  funext z
  simp only [mollify, translationPairing, convolution_eq_swap,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change u x * φ.normed μ (x - z) = φ.normed μ (z - x) * u x
    have hφ : φ.normed μ (x - z) = φ.normed μ (z - x) := by
      rw [← φ.normed_neg (x - z), neg_sub]
    rw [hφ, mul_comm])

theorem contDiff_mollify {u : E → ℝ} (hu : LocallyIntegrable u μ)
    (φ : ContDiffBump (0 : E)) {n : ℕ∞} : ContDiff ℝ n (mollify μ u φ) :=
  contDiff_translationPairing hu φ.hasCompactSupport_normed φ.contDiff_normed

/-- Averaging against a normalized nonnegative bump preserves a uniform
almost-everywhere absolute bound. -/
theorem abs_mollify_le_of_ae_abs_le
    {u : E → ℝ} (hu : LocallyIntegrable u μ) {C : ℝ} (_hC : 0 ≤ C)
    (huC : ∀ᵐ x ∂μ, |u x| ≤ C) (φ : ContDiffBump (0 : E)) (z : E) :
    |mollify μ u φ z| ≤ C := by
  have hpair : Integrable
      (fun x : E ↦ u x * φ.normed μ (x - z)) μ :=
    integrable_translationPairing hu φ.hasCompactSupport_normed
      φ.continuous_normed z
  have hleft : Integrable
      (fun x : E ↦ |u x| * φ.normed μ (x - z)) μ := by
    convert hpair.norm using 1
    funext x
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (φ.nonneg_normed (x - z))]
  have hright : Integrable
      (fun x : E ↦ C * φ.normed μ (x - z)) μ :=
    integrable_translationPairing (locallyIntegrable_const C)
      φ.hasCompactSupport_normed φ.continuous_normed z
  calc
    |mollify μ u φ z| =
        |∫ x : E, u x * φ.normed μ (x - z) ∂μ| := rfl
    _ ≤ ∫ x : E, |u x * φ.normed μ (x - z)| ∂μ :=
      abs_integral_le_integral_abs
    _ = ∫ x : E, |u x| * φ.normed μ (x - z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [abs_mul, abs_of_nonneg (φ.nonneg_normed (x - z))]
    _ ≤ ∫ x : E, C * φ.normed μ (x - z) ∂μ := by
      apply integral_mono_ae hleft hright
      filter_upwards [huC] with x hx
      exact mul_le_mul_of_nonneg_right hx (φ.nonneg_normed (x - z))
    _ = C := by
      rw [integral_const_mul, integral_sub_right_eq_self, φ.integral_normed, mul_one]

/-- The full topological support, including its boundary, is controlled by
the outer radius after translating the kernel to its center. -/
theorem tsupport_mollifier_translate_subset (φ : ContDiffBump (0 : E)) (z : E) :
    tsupport (fun x => φ.normed μ (x - z)) ⊆ closedBall z φ.rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hx' : x - z ∈ Function.support (φ.normed μ) := hx
  rw [φ.support_normed_eq] at hx'
  have hnorm : ‖x - z‖ < φ.rOut := by
    simpa only [mem_ball, dist_zero_right] using hx'
  simpa only [mem_closedBall, dist_eq_norm] using hnorm.le

/-- Lebesgue differentiation applies to these actual normalized kernels;
the density is only locally integrable. -/
theorem ae_tendsto_mollify {u : E → ℝ} (hu : LocallyIntegrable u μ)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ x ∂μ, Tendsto (fun n => mollify μ u (shrinkingBump R hR n) x)
      atTop (𝓝 (u x)) := by
  simp_rw [mollify_eq_convolution]
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (tendsto_shrinkingBump_rOut R hR) (K := 2) _ hu
  exact Eventually.of_forall (fun n => (shrinkingBump_radius_ratio R hR n).le)

end SGPT.Foundations.Analysis
