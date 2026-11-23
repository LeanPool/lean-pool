/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.Definitions

/-! # Growth comparisons for logarithmic order -/

public section

open Filter
open scoped ENNReal

namespace Bruck

theorem logOrder_le_of_eventually_rpow {F : ℝ → ℝ} {s : ℝ}
    (hpos : ∀ᶠ r in atTop, 0 < F r) (h : ∀ᶠ r in atTop, F r ≤ r ^ s) :
    logOrder F ≤ ENNReal.ofReal s := by
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hpos, h, eventually_gt_atTop (1 : ℝ)] with r hF hr h1
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (Real.log_pos h1)).2
  have hlog := Real.log_le_log hF hr
  rw [Real.log_rpow (zero_lt_one.trans h1)] at hlog
  simpa only [mul_comm] using hlog

theorem le_logOrder_of_frequently_rpow {F : ℝ → ℝ} {s : ℝ}
    (h : ∃ᶠ r in atTop, r ^ s ≤ F r) :
    ENNReal.ofReal s ≤ logOrder F := by
  refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  refine (h.and_eventually (eventually_gt_atTop (1 : ℝ))).mono ?_
  rintro r ⟨hr, h1⟩
  have hr0 := zero_lt_one.trans h1
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (Real.log_pos h1)).2
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hr0 s) hr
  rw [Real.log_rpow hr0] at hlog
  simpa only [mul_comm] using hlog

theorem eventually_le_rpow_of_logOrder_lt {F : ℝ → ℝ} {s : ℝ}
    (hpos : ∀ᶠ r in atTop, 0 < F r) (h : logOrder F < ENNReal.ofReal s) :
    ∀ᶠ r in atTop, F r ≤ r ^ s := by
  have hlt : ∀ᶠ r : ℝ in atTop,
      ENNReal.ofReal (Real.log (F r) / Real.log r) < ENNReal.ofReal s :=
    eventually_lt_of_limsup_lt h
  filter_upwards [hpos, hlt, eventually_gt_atTop (1 : ℝ)] with r hF hr h1
  have hquot : Real.log (F r) / Real.log r < s :=
    lt_of_not_ge fun hs => not_lt_of_ge (ENNReal.ofReal_le_ofReal hs) hr
  have hlog := (div_lt_iff₀ (Real.log_pos h1)).1 hquot
  have hr0 := zero_lt_one.trans h1
  apply (Real.log_le_log_iff hF (Real.rpow_pos_of_pos hr0 s)).1
  rw [Real.log_rpow hr0]
  simpa only [mul_comm] using hlog.le

/-- A fixed scale on the radius and a fixed positive multiplier do not increase
the logarithmic order in a one-sided growth comparison. -/
theorem logOrder_le_of_eventually_le_scaled {F G : ℝ → ℝ} {a k : ℝ}
    (ha : 0 < a) (hk : 0 < k)
    (hF : ∀ᶠ r in atTop, 0 < F r) (hG : ∀ᶠ r in atTop, 0 < G r)
    (h : ∀ᶠ r in atTop, F r ≤ a * G (k * r)) :
    logOrder F ≤ logOrder G := by
  by_contra! hlt
  obtain ⟨b, hb, hbF⟩ := exists_between hlt
  obtain ⟨d, hbd, hdF⟩ := exists_between hbF
  have hbtop := (hbF.trans_le le_top).ne
  have hdtop := (hdF.trans_le le_top).ne
  have hbdR : b.toReal < d.toReal := (ENNReal.toReal_lt_toReal hbtop hdtop).2 hbd
  have hbG : logOrder G < ENNReal.ofReal b.toReal := by
    rwa [ENNReal.ofReal_toReal hbtop]
  have hGbound := eventually_le_rpow_of_logOrder_lt hG hbG
  have hkTop : Tendsto (fun r : ℝ => k * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hk).2 tendsto_id
  have hrpow := (tendsto_rpow_atTop (sub_pos.2 hbdR)).eventually_ge_atTop
    (a * k ^ b.toReal)
  have hFbound : ∀ᶠ r in atTop, F r ≤ r ^ d.toReal := by
    filter_upwards [h, hkTop.eventually hGbound, hrpow, eventually_gt_atTop (0 : ℝ)]
      with r hcomp hGr hr hr0
    change G (k * r) ≤ (k * r) ^ b.toReal at hGr
    change a * k ^ b.toReal ≤ r ^ (d.toReal - b.toReal) at hr
    calc
      F r ≤ a * G (k * r) := hcomp
      _ ≤ a * (k * r) ^ b.toReal := mul_le_mul_of_nonneg_left hGr ha.le
      _ = (a * k ^ b.toReal) * r ^ b.toReal := by rw [Real.mul_rpow hk.le hr0.le, mul_assoc]
      _ ≤ r ^ (d.toReal - b.toReal) * r ^ b.toReal :=
        mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hr0.le _)
      _ = r ^ d.toReal := by rw [← Real.rpow_add hr0, sub_add_cancel]
  have hle := logOrder_le_of_eventually_rpow hF hFbound
  rw [ENNReal.ofReal_toReal hdtop] at hle
  exact (not_lt_of_ge hle) hdF

/-- Additive errors before a logarithm are harmless in logarithmic order when
both arguments tend to infinity. -/
theorem logOrder_log_le_of_eventually_le_affine {F G : ℝ → ℝ} {a k c : ℝ}
    (_ha : 0 < a) (hk : 0 < k) (hc : 0 ≤ c)
    (hF : Tendsto F atTop atTop) (hG : Tendsto G atTop atTop)
    (h : ∀ᶠ r in atTop, F r ≤ a * G (k * r) + c) :
    logOrder (fun r => Real.log (F r)) ≤ logOrder (fun r => Real.log (G r)) := by
  have hFpos : ∀ᶠ r in atTop, 0 < Real.log (F r) :=
    (hF.eventually_gt_atTop 1).mono fun _ hr => Real.log_pos hr
  have hGpos : ∀ᶠ r in atTop, 0 < Real.log (G r) :=
    (hG.eventually_gt_atTop 1).mono fun _ hr => Real.log_pos hr
  let A := max 1 (a + c)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  refine logOrder_le_of_eventually_le_scaled (a := 2) (k := k) (by norm_num) hk hFpos hGpos ?_
  have hkTop : Tendsto (fun r : ℝ => k * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hk).2 tendsto_id
  filter_upwards [h, hF.eventually_gt_atTop 1,
    (hG.comp hkTop).eventually_ge_atTop A] with r hr hFr hGr
  change A ≤ G (k * r) at hGr
  have hGone : 1 ≤ G (k * r) := (le_max_left _ _).trans hGr
  have hFle : F r ≤ A * G (k * r) :=
    hr.trans (calc
      a * G (k * r) + c ≤ a * G (k * r) + c * G (k * r) := by
        exact add_le_add_right (le_mul_of_one_le_right hc hGone) _
      _ = (a + c) * G (k * r) := (add_mul _ _ _).symm
      _ ≤ A * G (k * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hGone))
  calc
    Real.log (F r) ≤ Real.log (A * G (k * r)) := Real.log_le_log (zero_lt_one.trans hFr) hFle
    _ = Real.log A + Real.log (G (k * r)) :=
      Real.log_mul hA.ne' (zero_lt_one.trans_le hGone).ne'
    _ ≤ 2 * Real.log (G (k * r)) := by linarith [Real.log_le_log hA hGr]

end Bruck
