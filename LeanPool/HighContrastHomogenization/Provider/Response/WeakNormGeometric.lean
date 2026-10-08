/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm

/-!
# High-contrast homogenization: Provider.Response.WeakNormGeometric

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The geometric sum of the scale weights

Both scale sums of the weak-norm estimate are closed by the geometric sum over
scales,

```
Σ_{k = -∞}^{t} 3^{(s - ρ/2)(k - t)} ≤ C/(2s - ρ),
```

used at the exponent `s - ρ/2 ∈ (0, 1)` on the bad event and at the exponent `s`
on the old scales, where the printed right side `C/(2s-ρ)` is `2/(s - ρ/2)` for
`C = 4`.  Reindexed by `j = t - k`, the sum is the ordinary geometric series in
the ratio `3^{-a}`, and the bound comes from the convexity estimate
`3^{-a} ≤ 1 - a/2` on `0 < a ≤ 1`: since `log 3 ≥ 1`,

```
3^{-a} ≤ e^{-a} ≤ (1 + a)^{-1} ≤ 1 - a/2,
```

the last step because `a(1-a) ≥ 0`.  The tail form is the same bound after the
common factor `3^{-aH}` of the old scales `k < t - H` is taken out.

Nothing here is specific to the seminorm; the module is placed beside it because
the weights it sums are the weights of the scale-average seminorm.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

/-! ## The geometric sum of the scale weights -/

/-- The scale weight at the scale `k = t - j` is the `j`-th power of the ratio
`3^{-a}`, which is what makes the printed scale sum geometric. -/
theorem rpow_three_neg_natCast (a : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(a * (j : ℝ))) = ((3 : ℝ) ^ (-a)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-a)) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-- The base of the scale weights is below `1 - a/2`. -/
theorem rpow_three_neg_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (3 : ℝ) ^ (-a) ≤ 1 - a / 2 := by
  have hlog : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hstep : Real.log 3 * (-a) ≤ 1 * (-a) :=
    mul_le_mul_of_nonpos_right hlog (by linarith only [ha])
  have hbase : (3 : ℝ) ^ (-a) = Real.exp (Real.log 3 * (-a)) :=
    Real.rpow_def_of_pos (by norm_num) (-a)
  have hpos : (0 : ℝ) < 1 + a := by linarith only [ha]
  have hexp : (1 : ℝ) + a ≤ Real.exp a := by
    have := Real.add_one_le_exp a
    linarith only [this]
  have hinv : (Real.exp a)⁻¹ ≤ (1 + a)⁻¹ := inv_anti₀ hpos hexp
  have hchord : (1 + a)⁻¹ ≤ 1 - a / 2 := by
    have hge : (1 : ℝ) ≤ (1 - a / 2) * (1 + a) := by nlinarith only [ha, ha1]
    calc (1 + a)⁻¹ = (1 + a)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (1 + a)⁻¹ * ((1 - a / 2) * (1 + a)) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
      _ = (1 - a / 2) * ((1 + a)⁻¹ * (1 + a)) := by ring
      _ = 1 - a / 2 := by rw [inv_mul_cancel₀ hpos.ne', mul_one]
  calc (3 : ℝ) ^ (-a) = Real.exp (Real.log 3 * (-a)) := hbase
    _ ≤ Real.exp (1 * (-a)) := Real.exp_le_exp.mpr hstep
    _ = (Real.exp a)⁻¹ := by rw [one_mul, Real.exp_neg]
    _ ≤ (1 + a)⁻¹ := hinv
    _ ≤ 1 - a / 2 := hchord

/-- **The geometric sum of the scale weights**: `Σ_{k ≤ t}3^{a(k-t)} ≤ 2/a` for
`0 < a ≤ 1`, applied at `a = s` and at `a = s - ρ/2`, where the printed bound
`C/(2s-ρ)` is `4/(2s-ρ) = 2/(s-ρ/2)`. -/
theorem tsum_rpow_three_neg_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) ≤ 2 / a := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hrle : (3 : ℝ) ^ (-a) ≤ 1 - a / 2 := rpow_three_neg_le ha ha1
  have hr1 : (3 : ℝ) ^ (-a) < 1 := by linarith only [hrle, ha]
  have hsum : ∑' j : ℕ, ((3 : ℝ) ^ (-a)) ^ j = (1 - (3 : ℝ) ^ (-a))⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hhalf : a / 2 ≤ 1 - (3 : ℝ) ^ (-a) := by linarith only [hrle]
  have hpos : (0 : ℝ) < a / 2 := by linarith only [ha]
  calc ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) = ∑' j : ℕ, ((3 : ℝ) ^ (-a)) ^ j :=
        tsum_congr fun j => rpow_three_neg_natCast a j
    _ = (1 - (3 : ℝ) ^ (-a))⁻¹ := hsum
    _ ≤ (a / 2)⁻¹ := inv_anti₀ hpos hhalf
    _ = 2 / a := by rw [inv_div]

/-- **The tail of the geometric sum**, the form in which the contribution of the
old scales `k < t - H` is summed. -/
theorem tsum_rpow_three_neg_shift_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) ≤ (3 : ℝ) ^ (-(a * (n : ℝ))) * (2 / a) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hfun : ∀ j : ℕ, (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ)))) =
      (3 : ℝ) ^ (-(a * (n : ℝ))) * (3 : ℝ) ^ (-(a * (j : ℝ))) := by
    intro j
    rw [← Real.rpow_add h3]
    ring_nf
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(a * (n : ℝ))) := Real.rpow_nonneg h3.le _
  calc ∑' j : ℕ, (3 : ℝ) ^ (-(a * ((j : ℝ) + (n : ℝ))))
      = ∑' j : ℕ, (3 : ℝ) ^ (-(a * (n : ℝ))) * (3 : ℝ) ^ (-(a * (j : ℝ))) := tsum_congr hfun
    _ = (3 : ℝ) ^ (-(a * (n : ℝ))) * ∑' j : ℕ, (3 : ℝ) ^ (-(a * (j : ℝ))) := tsum_mul_left
    _ ≤ (3 : ℝ) ^ (-(a * (n : ℝ))) * (2 / a) :=
        mul_le_mul_of_nonneg_left (tsum_rpow_three_neg_le ha ha1) hnn

/-- The scale weights form a summable family, so the printed scale sum has a
real value and the seminorm's majorants are finite. -/
theorem summable_rpow_three_neg {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Summable fun j : ℕ => (3 : ℝ) ^ (-(a * (j : ℝ))) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-a) < 1 := by
    have hrle : (3 : ℝ) ^ (-a) ≤ 1 - a / 2 := rpow_three_neg_le ha ha1
    linarith only [hrle, ha]
  refine (summable_geometric_of_lt_one hr0 hr1).congr fun j => ?_
  exact (rpow_three_neg_natCast a j).symm

end

end Response
end HighContrast
end HCPolySupport
