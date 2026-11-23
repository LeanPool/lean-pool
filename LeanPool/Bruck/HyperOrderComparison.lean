/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.HyperOrder
public import LeanPool.Bruck.PoissonBound
import LeanPool.Bruck.GrowthFacts

/-! # Maximum-modulus formulation and affine invariance of hyper-order -/

public section

open Filter Real

namespace Bruck

private theorem log_maximumModulus_le_three_characteristic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 1 ≤ r) :
    log (wvMaximumModulus f r) ≤ 3 * ValueDistribution.characteristic f ⊤ (2 * r) := by
  have hscale : (2 * r + r) / (2 * r - r) = 3 := by
    apply (div_eq_iff (by linarith : 2 * r - r ≠ 0)).2
    ring
  have hlog : log (wvMaximumModulus f r) ≤ log⁺ (wvMaximumModulus f r) := by
    rw [posLog_apply]
    exact le_max_right _ _
  apply hlog.trans
  simpa only [hscale] using posLog_maximumModulus_le_characteristic hf hr
    (show r < 2 * r by linarith)

/-- The characteristic of a nonconstant entire function tends to infinity. -/
theorem characteristic_tendsto_atTop {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) : Tendsto (ValueDistribution.characteristic f ⊤) atTop atTop := by
  have hhalf : Tendsto (fun r : ℝ => r / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hm := tendsto_log_atTop.comp ((maximumModulus_tendsto_atTop hf hnon).comp hhalf)
  refine tendsto_atTop_mono' atTop ?_ (hm.atTop_div_const (show (0 : ℝ) < 3 by norm_num))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hle := log_maximumModulus_le_three_characteristic hf (r := r / 2)
    (by linarith)
  rw [show 2 * (r / 2) = r by ring] at hle
  change log (wvMaximumModulus f (r / 2)) / 3 ≤ ValueDistribution.characteristic f ⊤ r
  linarith

/-- For a nonconstant entire function, the characteristic definition of hyper-order
equals the limsup given by the triple logarithm of its maximum modulus. -/
theorem hyperOrder_eq_logOrder_maximumModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) :
    hyperOrder f = logOrder (fun r => log (log (wvMaximumModulus f r))) := by
  have hm := maximumModulus_tendsto_atTop hf hnon
  have hlogM : Tendsto (fun r => log (wvMaximumModulus f r)) atTop atTop :=
    tendsto_log_atTop.comp hm
  have hchar := characteristic_tendsto_atTop hf hnon
  unfold hyperOrder
  refine le_antisymm ?_ ?_
  · refine logOrder_log_le_of_eventually_le_affine
      (a := 1) (k := 1) (c := 0) (by norm_num) le_rfl hchar hlogM ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ), hm.eventually_ge_atTop 1] with r hr hMr
    have hposLog : log⁺ (wvMaximumModulus f r) = log (wvMaximumModulus f r) :=
      posLog_eq_log (by rwa [abs_of_nonneg (wvMaximumModulus_nonneg f r)])
    simpa only [one_mul, add_zero, ← hposLog] using characteristic_le_posLog_maximumModulus hf hr
  · refine logOrder_log_le_of_eventually_le_affine
      (a := 3) (k := 2) (c := 0) (by norm_num) le_rfl hlogM hchar ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    simpa only [add_zero] using log_maximumModulus_le_three_characteristic hf hr

private theorem affine_error_nonneg (a b : ℂ) : 0 ≤ log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 :=
  add_nonneg (add_nonneg posLog_nonneg posLog_nonneg) (log_nonneg (by norm_num))

/-- An affine change with nonzero scale preserves the hyper-order of a
nonconstant entire function. -/
theorem hyperOrder_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    hyperOrder (fun z => a * f z + b) = hyperOrder f := by
  let g : ℂ → ℂ := fun z => a * f z + b
  have hg : Differentiable ℂ g := (hf.const_mul a).add_const b
  have hg_non : ¬ ∀ z, g z = g 0 := by
    intro hc
    apply hnon
    intro z
    exact mul_left_cancel₀ ha (add_right_cancel (hc z))
  have hcharF := characteristic_tendsto_atTop hf hnon
  have hcharG := characteristic_tendsto_atTop hg hg_non
  have hinv : (fun z => a⁻¹ * g z + -(a⁻¹ * b)) = f := by
    funext z
    simp only [g, mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, add_neg_cancel_right]
  change hyperOrder g = hyperOrder f
  unfold hyperOrder
  refine le_antisymm ?_ ?_
  · refine logOrder_log_le_of_eventually_le_affine
      (a := 1) (k := 1) (c := log⁺ ‖a‖ + log⁺ ‖b‖ + log 2)
      (by norm_num) (affine_error_nonneg a b) hcharG hcharF
      (Eventually.of_forall fun r => ?_)
    simpa only [one_mul] using characteristic_affine_le hf a b r
  · refine logOrder_log_le_of_eventually_le_affine
      (a := 1) (k := 1) (c := log⁺ ‖a⁻¹‖ + log⁺ ‖-(a⁻¹ * b)‖ + log 2)
      (by norm_num) (affine_error_nonneg a⁻¹ (-(a⁻¹ * b))) hcharF hcharG
      (Eventually.of_forall fun r => ?_)
    simpa only [one_mul, hinv] using characteristic_affine_le hg a⁻¹ (-(a⁻¹ * b)) r

end Bruck
