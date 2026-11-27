/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.ZeroSet

/-!
# Real Lipschitz functions on `ℝ^m`: derivatives almost everywhere

Facts about the derivatives of Lipschitz functions `f, g : ℝ^m → ℝ` (`ℝ^m = Fin m → ℝ`), which
exist almost everywhere by Rademacher's theorem. They are standard.

* `ae_fderiv_eq_zero_of_eq_zero`: the derivative vanishes almost everywhere on the zero set (the
  real-valued form of `rd_ae_fderiv_eq_zero`);
* `ae_fderiv_max_eq_or`: almost everywhere, the derivative of `max f g` is that of `f` or that of
  `g`;
* `tendsto_slope_of_differentiableAt`: the difference quotient `t⁻¹ (f (x + t v) − f (x))` tends
  to `∂_v f (x)` where `f` is differentiable;
* `abs_slope_le_of_lipschitzWith`: the difference quotients of a `K`-Lipschitz `f` in a direction
  `v` are bounded by `K ‖v‖`;
* `tendsto_setIntegral_slope_mul`: the integral over a set of finite measure of the product of two
  difference quotients in a direction `v` tends to `∫ ∂_v f ∂_v g` (dominated convergence).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CalculusOfVariations

variable {m : ℕ}

/-- The derivative of a real Lipschitz function vanishes almost everywhere on its zero set (the
real-valued form of `rd_ae_fderiv_eq_zero`). -/
theorem ae_fderiv_eq_zero_of_eq_zero {f : (Fin m → ℝ) → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), f x = 0 → fderiv ℝ f x = 0 := by
  have hφ : LipschitzWith K (fun x (_ : Fin 1) => f x) :=
    LipschitzWith.of_dist_le_mul fun x y => by rw [dist_pi_const]; exact hf.dist_le_mul x y
  filter_upwards [rd_ae_fderiv_eq_zero hφ, hf.ae_differentiableAt] with x hx hdiff h0
  have h1 : HasFDerivAt (fun x (_ : Fin 1) => f x)
      (ContinuousLinearMap.pi fun _ => fderiv ℝ f x) x :=
    hasFDerivAt_pi'.2 fun _ => hdiff.hasFDerivAt
  have h2 := hx (funext fun _ => h0)
  rw [h1.fderiv] at h2
  ext v
  simpa using congrArg (fun L => L v 0) h2

/-- **The derivative of a maximum.** For real Lipschitz `f`, `g`, almost everywhere the derivative
of `max f g` is the derivative of `f` or that of `g`: where `f > g` or `f < g` the maximum is
locally `f` or `g`, and almost everywhere on `{f = g}` the derivative of `max f g − g` vanishes
(the zero-set lemma `ae_fderiv_eq_zero_of_eq_zero`). -/
theorem ae_fderiv_max_eq_or {f g : (Fin m → ℝ) → ℝ} {Kf Kg : NNReal} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      fderiv ℝ (fun y => max (f y) (g y)) x = fderiv ℝ f x ∨
        fderiv ℝ (fun y => max (f y) (g y)) x = fderiv ℝ g x := by
  have hM := hf.max hg
  filter_upwards [ae_fderiv_eq_zero_of_eq_zero (hM.sub hg), hg.ae_differentiableAt,
    hM.ae_differentiableAt] with x h0 hgd hMd
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · right
    apply EventuallyEq.fderiv_eq
    filter_upwards [hf.continuous.continuousAt.eventually_lt hg.continuous.continuousAt hlt]
      with y hy
    exact max_eq_right hy.le
  · right
    have h := h0 (by simp [heq])
    rw [fderiv_fun_sub hMd hgd, sub_eq_zero] at h
    exact h
  · left
    apply EventuallyEq.fderiv_eq
    filter_upwards [hg.continuous.continuousAt.eventually_lt hf.continuous.continuousAt hgt]
      with y hy
    exact max_eq_left hy.le

/-- The difference quotient `t⁻¹ (f (x + t v) − f (x))` of a differentiable `f` tends to
`∂_v f (x)` as `t → 0`, `t ≠ 0`. -/
theorem tendsto_slope_of_differentiableAt {f : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (hf : DifferentiableAt ℝ f x) (v : Fin m → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * (f (x + t • v) - f x)) (𝓝[≠] 0) (𝓝 (fderiv ℝ f x v)) := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
    have h3 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]; exact hf.hasFDerivAt
    exact h3.comp_hasDerivAt (0 : ℝ) h1
  simpa using h2.tendsto_slope_zero

/-- `|t⁻¹ (f (x + t v) − f (x))| ≤ K ‖v‖` for a `K`-Lipschitz `f`. -/
theorem abs_slope_le_of_lipschitzWith {f : (Fin m → ℝ) → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (x v : Fin m → ℝ) (t : ℝ) : |t⁻¹ * (f (x + t • v) - f x)| ≤ K * ‖v‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_smul, add_zero, sub_self, mul_zero, abs_zero]
    positivity
  have h := hf.dist_le_mul (x + t • v) x
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
  rw [abs_mul, abs_inv]
  calc |t|⁻¹ * |f (x + t • v) - f x| ≤ |t|⁻¹ * (K * (|t| * ‖v‖)) := by
        gcongr; rwa [← Real.norm_eq_abs]
    _ = K * ‖v‖ := by field_simp

/-- **Difference quotients and dominated convergence.** For real Lipschitz `f`, `g`, a direction
`v` and a set `s` of finite measure,
`∫_s t⁻¹ (f (x + t v) − f x) · t⁻¹ (g (x + t v) − g x) dx → ∫_s ∂_v f ∂_v g` as `t → 0`. -/
theorem tendsto_setIntegral_slope_mul {f g : (Fin m → ℝ) → ℝ} {Kf Kg : NNReal}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) (v : Fin m → ℝ)
    {s : Set (Fin m → ℝ)} (hs : volume s ≠ ⊤) :
    Tendsto (fun t : ℝ => ∫ x in s,
        (t⁻¹ * (f (x + t • v) - f x)) * (t⁻¹ * (g (x + t • v) - g x)))
      (𝓝[≠] 0) (𝓝 (∫ x in s, fderiv ℝ f x v * fderiv ℝ g x v)) := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (Kf * ‖v‖) * (Kg * ‖v‖))
    (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    (integrable_const _) ?_
  · have hcf := hf.continuous
    have hcg := hg.continuous
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_slope_le_of_lipschitzWith hf x v t)
      (abs_slope_le_of_lipschitzWith hg x v t) (abs_nonneg _) (by positivity)
  · filter_upwards [ae_restrict_of_ae hf.ae_differentiableAt,
      ae_restrict_of_ae hg.ae_differentiableAt] with x hfx hgx
    exact (tendsto_slope_of_differentiableAt hfx v).mul (tendsto_slope_of_differentiableAt hgx v)

end CalculusOfVariations
