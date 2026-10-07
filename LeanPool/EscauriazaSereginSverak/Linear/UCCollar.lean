/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCDefs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian weight on the cutoff collar

The weight in `lem:uc-gaussian` is exponentially small where the spatial
or final-time cutoff changes.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem uc_log_weight_formula {s : ℝ} (hs : 0 < s) :
    Real.log (gaussCarlemanTimeWeight s) =
      Real.log s + (1 - s) / 3 := by
  rw [gaussCarlemanTimeWeight, Real.log_mul hs.ne' (Real.exp_ne_zero _),
    Real.log_exp]

/-- Numerical bounds for the time weight at the Gaussian cutoff threshold
(`eq:uc-collar-weight`). -/
theorem uc_log_weight_three_half_bounds :
    (1 / 5 : ℝ) ≤ Real.log (gaussCarlemanTimeWeight (3 / 2)) ∧
      Real.log (gaussCarlemanTimeWeight (3 / 2)) ≤ 2 / 3 := by
  have hformula := uc_log_weight_formula (s := (3 / 2 : ℝ)) (by norm_num)
  have hlo := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have hhi := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  constructor <;> rw [hformula]
  · norm_num at hlo ⊢
    linarith only [hlo]
  · norm_num at hhi ⊢
    linarith only [hhi]

private theorem uc_log_weight_lower {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    Real.log (gaussCarlemanTimeWeight (3 / 2)) - 1 / s ≤
      Real.log (gaussCarlemanTimeWeight s) := by
  have hlog := Real.one_sub_inv_le_log_of_pos hs
  have hL := uc_log_weight_three_half_bounds.2
  rw [uc_log_weight_formula hs]
  have hsle : s ≤ 2 := le_of_lt hs2
  linarith only [hlog, hL, hsle, inv_eq_one_div s]

private theorem uc_log_weight_final_time {s : ℝ}
    (hs : 3 / 2 ≤ s) (hs2 : s < 2) :
    Real.log (gaussCarlemanTimeWeight (3 / 2)) ≤
      Real.log (gaussCarlemanTimeWeight s) := by
  have hspos : 0 < s := by linarith only [hs]
  have hratio : 0 < s / (3 / 2 : ℝ) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hlogratio : Real.log (s / (3 / 2 : ℝ)) =
      Real.log s - Real.log (3 / 2 : ℝ) := by
    exact Real.log_div hspos.ne' (by norm_num)
  rw [hlogratio] at hlog
  rw [uc_log_weight_formula hspos,
    uc_log_weight_formula (show (0 : ℝ) < 3 / 2 by norm_num)]
  have hsle : s ≤ 2 := le_of_lt hs2
  have hsdiff : 0 ≤ s - 3 / 2 := by linarith only [hs]
  have hdiv : (s - 3 / 2) / 3 ≤ 1 - (s / (3 / 2 : ℝ))⁻¹ := by
    have hsinv : (s / (3 / 2 : ℝ))⁻¹ = (3 / 2) / s := by field_simp
    rw [hsinv]
    have hprod : (s - 3 / 2) * s ≤ (s - 3 / 2) * 3 :=
      mul_le_mul_of_nonneg_left (by linarith only [hsle]) hsdiff
    calc
      (s - 3 / 2) / 3 ≤ (s - 3 / 2) / s :=
        (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hspos).2 hprod
      _ = 1 - (3 / 2) / s := by field_simp
  linarith only [hlog, hdiv]

/-- The Gaussian weight is exponentially small on the spatial and final-time
collar (`eq:uc-collar-weight`). -/
theorem uc_gaussian_collar_weight
    (ρ : ℝ) (hρ : 4 ≤ ρ) (z : ParabolicPoint)
    (hz : z ∈ ucCutoffRegion ρ) :
    ucGaussianWeight ((1 / 100) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2)))) z ≤
      Real.exp (-(ρ ^ 2) / 100) := by
  let L : ℝ := Real.log (gaussCarlemanTimeWeight (3 / 2))
  have hL : 1 / 5 ≤ L := uc_log_weight_three_half_bounds.1
  have hLpos : 0 < L := by linarith only [hL]
  have hs : 0 < z.2 := hz.1.2.1
  have hs2 : z.2 < 2 := hz.1.2.2
  have hweight : 0 < gaussCarlemanTimeWeight z.2 := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hcancel : ρ ^ 2 / (100 * L) * L = ρ ^ 2 / 100 := by
    field_simp
  rw [ucGaussianWeight, Real.rpow_def_of_pos hweight]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hrewrite :
      Real.log (gaussCarlemanTimeWeight z.2) *
          (-2 * ((1 / 100 : ℝ) * ρ ^ 2 / (2 * L))) +
        -(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2) =
      -(ρ ^ 2 / (100 * L) *
          Real.log (gaussCarlemanTimeWeight z.2)) -
        vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) := by ring
  rw [hrewrite]
  by_cases htime : 3 / 2 ≤ z.2
  · have hlog := uc_log_weight_final_time htime hs2
    change L ≤ Real.log (gaussCarlemanTimeWeight z.2) at hlog
    have hnorm : 0 ≤ vec3EuclideanNorm z.1 ^ 2 := sq_nonneg _
    have hden : 0 < 4 * z.2 := by positivity
    have hfrac : 0 ≤ vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) :=
      div_nonneg hnorm hden.le
    have hcoef : 0 ≤ ρ ^ 2 / (100 * L) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hcoef
    rw [hcancel] at hmul
    linarith only [hmul, hfrac]
  · have hspace : ρ / 2 ≤ vec3EuclideanNorm z.1 := by
      have hnot : z.1 ∉ vec3Ball 0 (ρ / 2) := by
        intro hmem
        apply hz.2
        exact ⟨hmem, hs, lt_of_not_ge htime⟩
      simpa only [mem_vec3Ball, sub_zero, not_lt] using hnot
    have hnorm : (1 / 4 : ℝ) * ρ ^ 2 ≤ vec3EuclideanNorm z.1 ^ 2 := by
      have hp : 0 ≤ ρ / 2 := by linarith only [hρ]
      nlinarith only [hspace, hp, sq_nonneg (vec3EuclideanNorm z.1)]
    have hlog := uc_log_weight_lower hs hs2
    change L - 1 / z.2 ≤ Real.log (gaussCarlemanTimeWeight z.2) at hlog
    have hcoef : 0 ≤ ρ ^ 2 / (100 * L) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hcoef
    have hρsq : 0 ≤ ρ ^ 2 := sq_nonneg _
    have hnumeric : ρ ^ 2 / (100 * L * z.2) ≤
        (1 / 4 : ℝ) * ρ ^ 2 / (4 * z.2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 100 * L * z.2)
        (by positivity : 0 < 4 * z.2)).2
      nlinarith only [hL, hρsq, hs.le, mul_nonneg hρsq hs.le]
    have hgauss : (1 / 4 : ℝ) * ρ ^ 2 / (4 * z.2) ≤
        vec3EuclideanNorm z.1 ^ 2 / (4 * z.2) := by
      exact div_le_div_of_nonneg_right hnorm (by positivity)
    rw [mul_sub, hcancel] at hmul
    have hmul' : ρ ^ 2 / 100 - ρ ^ 2 / (100 * L * z.2) ≤
        ρ ^ 2 / (100 * L) * Real.log (gaussCarlemanTimeWeight z.2) := by
      convert hmul using 1
      ring
    linarith only [hmul', hnumeric, hgauss]

end ESS
