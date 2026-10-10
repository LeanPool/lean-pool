/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Real exponential and logarithmic estimates used in the analytic KAM bounds.
-/

@[expose] public section

namespace KamProject.Arnold1963

theorem rpow_mul_exp_neg_le {x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    x ^ v * Real.exp (-x) ≤ (v / Real.exp 1) ^ v := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hv)
  have h : v * Real.log (x / v) ≤ x - v := by
    calc
      _ ≤ v * (x / v - 1) := mul_le_mul_of_nonneg_left hlog hv.le
      _ = x - v := by field_simp
  rw [Real.log_div hx.ne' hv.ne'] at h
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (div_pos hv (Real.exp_pos 1)),
    ← Real.exp_add, Real.exp_le_exp, Real.log_div hv.ne' (Real.exp_ne_zero 1),
    Real.log_exp]
  nlinarith

theorem rpow_le_scaled_exp {m v δ : ℝ} (hm : 0 < m) (hv : 0 < v) (hδ : 0 < δ) :
    m ^ v ≤ (v / Real.exp 1) ^ v * δ ^ (-v) * Real.exp (m * δ) := by
  have h := rpow_mul_exp_neg_le (mul_pos hm hδ) hv
  rw [Real.rpow_def_of_pos (mul_pos hm hδ), ← Real.exp_add,
    Real.rpow_def_of_pos (div_pos hv (Real.exp_pos 1)), Real.exp_le_exp,
    Real.log_mul hm.ne' hδ.ne'] at h
  rw [Real.rpow_def_of_pos hm, Real.rpow_def_of_pos (div_pos hv (Real.exp_pos 1)),
    Real.rpow_def_of_pos hδ, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith

theorem log_le_rpow {x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    Real.log x ≤ (v / Real.exp 1) * x ^ (1 / v) := by
  have h := mul_le_mul_of_nonneg_right
    (Real.mul_exp_neg_le_exp_neg_one (Real.log x / v))
    (mul_pos hv (Real.exp_pos (Real.log x / v))).le
  have hl : (Real.log x / v * Real.exp (-(Real.log x / v))) *
      (v * Real.exp (Real.log x / v)) = Real.log x := by
    rw [Real.exp_neg]
    field_simp
  rw [hl] at h
  calc
    Real.log x ≤ Real.exp (-1) * (v * Real.exp (Real.log x / v)) := h
    _ = (v / Real.exp 1) * x ^ (1 / v) := by
      rw [Real.rpow_def_of_pos hx, Real.exp_neg]
      simp only [div_eq_mul_inv, one_mul]
      ring

theorem rpow_mul_exp_neg_mul_le {m v δ : ℝ} (hm : 0 < m) (hv : 0 < v) (hδ : 0 < δ) :
    m ^ v * Real.exp (-(m * δ)) ≤ (v / Real.exp 1) ^ v * δ ^ (-v) := by
  have h := mul_le_mul_of_nonneg_right (rpow_le_scaled_exp hm hv hδ)
    (Real.exp_pos (-(m * δ))).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using h

theorem log_inv_le_rpow {δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v) :
    Real.log (1 / δ) ≤ (v / Real.exp 1) * δ ^ (-(1 / v)) := by
  simpa only [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le] using
    (log_le_rpow (inv_pos.mpr hδ) hv)

theorem half_le_one_sub_exp_neg {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ / 2 ≤ 1 - Real.exp (-δ) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp δ) (Real.exp_pos (-δ)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have hprod : 1 ≤ (δ + 1) * (1 - δ / 2) := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have he : Real.exp (-δ) ≤ 1 - δ / 2 :=
    le_of_mul_le_mul_left (h.trans hprod) (by linarith : 0 < δ + 1)
  linarith

end KamProject.Arnold1963
