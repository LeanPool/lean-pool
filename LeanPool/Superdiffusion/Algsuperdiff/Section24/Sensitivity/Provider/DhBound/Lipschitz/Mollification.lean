/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import Mathlib.Analysis.Convolution

/-!
# Mollification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `L^∞` control and weak-derivative bookkeeping for the convex-domain smoothing

This module supplies the two elementary facts that the `W^{1,∞}`-to-Lipschitz
bridge needs about the CoarseGraining convex-domain mollifier
`Homogenization.convexApproxSmoothRepresentative`:

* `abs_convexApproxSmoothRepresentative_le`: the mollifier is an averaging
  operator, hence it never increases a uniform bound.  This is exactly
  Mathlib's `dist_convolution_le` applied at `z₀ = 0`, using that the scaled
  convex-approximation kernel is nonnegative, compactly supported, and has unit
  integral.
* `HasWeakPartialDerivOn.congr_deriv_ae`: the weak-derivative relation only sees
  the derivative field through an integral against test functions, so it is
  invariant under a.e. modification of that field.  This lets one replace a
  derivative field bounded *almost everywhere* by its truncation, which is
  bounded *everywhere* — the form needed by the convolution estimate above.

The truncation itself is packaged as `boundedTruncation`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

open HCPolySupport MeasureTheory
open scoped ENNReal Convolution

variable {d : ℕ}

/-! ## Support of the scaled kernel -/

/-- The scaled convex-approximation kernel at scale `a` is supported in the ball
of radius `a + 1` about the origin. -/
theorem support_scaledConvexApproxKernel_subset_ball
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {a : ℝ} (ha : 0 < a) :
    Function.support (scaledConvexApproxKernel ρ a) ⊆ Metric.ball (0 : Vec d) (a + 1) := by
  intro y hy
  have hy' : ρ (a⁻¹ • y) ≠ 0 := by
    intro hzero
    exact hy (by simp [scaledConvexApproxKernel, hzero])
  have hmem : a⁻¹ • y ∈ tsupport ρ := subset_tsupport ρ hy'
  have hball : ‖a⁻¹ • y‖ ≤ 1 := by
    have := hρ.support_subset_closedBall hmem
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have hscaled : a⁻¹ * ‖y‖ ≤ 1 := by
    simpa [norm_smul, abs_inv, abs_of_pos ha] using hball
  have hmul := mul_le_mul_of_nonneg_left hscaled ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_one] at hmul
  have : ‖y‖ < a + 1 := by linarith
  simpa [Metric.mem_ball, dist_zero_right] using this

/-! ## `L^∞` preservation -/

/-- **The mollifier does not increase a uniform bound.**  If `w` is bounded by
`B` on `U`, then the globally smooth representative
`convexApproxSmoothRepresentative U ρ w x0 r ε` is bounded by `B` everywhere. -/
theorem abs_convexApproxSmoothRepresentative_le
    {U : Set (Vec d)} {ρ w : Vec d → ℝ} (hU : MeasurableSet U)
    (hρ : IsConvexApproxKernel ρ) (hw : MemLpOn U ∞ w)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y ∈ U, |w y| ≤ B)
    {x0 : Vec d} {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε) (x : Vec d) :
    |convexApproxSmoothRepresentative U ρ w x0 r ε x| ≤ B := by
  have hεr : 0 < ε * r := by positivity
  have hind : MemLp (Set.indicator U w) ∞ (volume : Measure (Vec d)) :=
    (MeasureTheory.memLp_indicator_iff_restrict hU).mpr hw
  have hpoint : ∀ y ∈ Metric.ball ((1 - ε) • x + ε • x0) (ε * r + 1),
      dist (Set.indicator U w y) (0 : ℝ) ≤ B := by
    intro y _
    by_cases hy : y ∈ U
    · simpa [Set.indicator_of_mem hy, Real.dist_eq] using hbound y hy
    · simpa [Set.indicator_of_notMem hy, Real.dist_eq] using hB
  have hconv :=
    dist_convolution_le (μ := (volume : Measure (Vec d))) (z₀ := (0 : ℝ))
      (x₀ := (1 - ε) • x + ε • x0) hB
      (support_scaledConvexApproxKernel_subset_ball hρ hεr)
      (fun y => scaledConvexApproxKernel_nonneg hρ hεr y)
      (integral_scaledConvexApproxKernel hρ hεr)
      hind.aestronglyMeasurable hpoint
  simpa [convexApproxSmoothRepresentative, Real.dist_eq] using hconv

/-! ## Congruence of the weak-derivative relation -/

/-- The weak partial derivative relation is invariant under a.e. modification of
the derivative field. -/
theorem HasWeakPartialDerivOn.congr_deriv_ae
    {U : Set (Vec d)} {i : Fin d} {u g g' : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u g)
    (hgg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDerivOn U i u g' := by
  intro φ hφ_smooth hφ_compact hφ_sub
  have hint : ∫ x in U, g x * φ x ∂(volume : Measure (Vec d)) =
      ∫ x in U, g' x * φ x ∂(volume : Measure (Vec d)) :=
    MeasureTheory.integral_congr_ae (hgg.mono fun x hx => by simp [hx])
  rw [h φ hφ_smooth hφ_compact hφ_sub, hint]

/-! ## Truncation of a field to a uniform bound -/

/-- The truncation of `f` to the interval `[-B, B]`. -/
noncomputable def boundedTruncation (B : ℝ) (f : Vec d → ℝ) : Vec d → ℝ :=
  fun x => max (-B) (min B (f x))

theorem continuous_truncationMap (B : ℝ) :
    Continuous fun t : ℝ => max (-B) (min B t) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_boundedTruncation_le {B : ℝ} (hB : 0 ≤ B) (f : Vec d → ℝ) (x : Vec d) :
    |boundedTruncation B f x| ≤ B := by
  have hmin : min B (f x) ≤ B := min_le_left _ _
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) hmin

theorem boundedTruncation_eq_self {B : ℝ} {f : Vec d → ℝ} {x : Vec d}
    (hx : |f x| ≤ B) : boundedTruncation B f x = f x := by
  rw [abs_le] at hx
  rw [boundedTruncation, min_eq_right hx.2, max_eq_right hx.1]

theorem boundedTruncation_ae_eq {U : Set (Vec d)} {B : ℝ} {f : Vec d → ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict U), |f x| ≤ B) :
    f =ᵐ[volume.restrict U] boundedTruncation B f :=
  hf.mono fun _ hx => (boundedTruncation_eq_self hx).symm

theorem memLpOn_top_boundedTruncation {U : Set (Vec d)} {B : ℝ} (hB : 0 ≤ B)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f (volume.restrict U)) :
    MemLpOn U ∞ (boundedTruncation B f) := by
  refine MeasureTheory.memLp_top_of_bound
    ((continuous_truncationMap B).comp_aestronglyMeasurable hf) B ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using abs_boundedTruncation_le hB f x

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
