/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor

/-!
CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree.

Uniform comparison of logarithmic coefficient-height ratios.
-/

@[expose] public section
namespace CCDN

private lemma weighted_exp_ratio_le {u v a r : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 0 < a) (hr : 1 ≤ r) (hra : 1 ≤ r * a) :
    (v + a) / Real.exp v ≤ r * ((u + a) / Real.exp u) := by
  have ht : 0 ≤ v - u := sub_nonneg.mpr huv
  have hru : 1 ≤ r * (u + a) := by nlinarith
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh : v + a ≤ r * (u + a) * Real.exp (v - u) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ u + a by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hru) ht
    have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ r * (u + a) by positivity)
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).mpr
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hh'
  exact hh'

/-- Replace an upper height by any lower height with a dimension-only loss. -/
private theorem logarithmic_height_ratio_le {H Y q c r : ℝ}
    (hY : 1 ≤ Y) (hYH : Y ≤ H) (hq : 0 < q) (hc : 0 < c)
    (hr : 1 ≤ r) (hrqc : 1 ≤ r * (q * c)) :
    (Real.log H + c) / H ^ q ≤ r * ((Real.log Y + c) / Y ^ q) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hu : 0 ≤ q * Real.log Y := mul_nonneg hq.le (Real.log_nonneg hY)
  have huv : q * Real.log Y ≤ q * Real.log H :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYH) hq.le
  have hh := weighted_exp_ratio_le hu huv (mul_pos hq hc) hr hrqc
  rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hY0]
  apply (mul_le_mul_iff_right₀ hq).mp
  rw [mul_comm (Real.log H) q, mul_comm (Real.log Y) q]
  convert hh using 1 <;> ring

end CCDN

namespace CCDN
noncomputable section

private lemma dimension_root_le_degree {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have he : 1 / (r : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hr1
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 he

/-- The coefficient-weighted ratio has loss at most r in dimension r. -/
theorem hypersurface_logarithmic_height_transfer {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {H Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H) :
    (Real.log H + (d : ℝ) ^ 2) / H ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  apply logarithmic_height_ratio_le hY hYH (by positivity) (by positivity) hr1
  have he : (r : ℝ) * (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))) * (d : ℝ) ^ 2) =
      (d : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) := by field_simp
  rw [he]
  exact (one_le_div hroot).mpr (dimension_root_le_degree hr hd)

/-- The exponent bookkeeping `d ^ (4 - 1 / (n + 1)) = d ^ (2 - 1 / (n + 1)) * d ^ 2` used by the
affine minimum and height-transfer estimates. -/
lemma rpow_four_sub_eq_mul_sq {d : ℝ} (hd : 0 < d) (n : ℕ) :
    d ^ (4 - 1 / (n + 1 : ℝ)) = d ^ (2 - 1 / (n + 1 : ℝ)) * d ^ 2 := by
  rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd]
  congr 1
  norm_num
  ring

/-- CCDN Lemma 4.2.3 with an explicit dimension constant. The coefficient
height is the maximum, and the bad-prime factor is the defined factor. -/
theorem hypersurface_badPrime_height_transfer {n d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hd : 0 < d)
    {Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ (integerCoefficientHeight f : ℝ)) :
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤
      ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)) *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) /
          Y ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let H := (integerCoefficientHeight f : ℝ)
  have hH : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let C := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hbad : hypersurfaceBadPrimeFactor f ≤ C * (1 + Real.log H / (d : ℝ) ^ 2) := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio : (Real.log H + (d : ℝ) ^ 2) / H ^ q ≤
      (n + 1 : ℝ) * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hypersurface_logarithmic_height_transfer (r := n + 1) (by omega) hd hY hYH
  have hpowers : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) =
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 :=
    rpow_four_sub_eq_mul_sq hd0 n
  have hstep : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f / H ^ q ≤
      C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((Real.log H + (d : ℝ) ^ 2) / H ^ q) := by
    calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * (C * (1 + Real.log H / (d : ℝ) ^ 2)) / H ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbad (by positivity)) (by positivity)
      _ = _ := by rw [hpowers]; field_simp; ring
  have hlast := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) by positivity)
  apply hstep.trans
  convert hlast using 1
  dsimp only [C]
  ring

end
end CCDN
