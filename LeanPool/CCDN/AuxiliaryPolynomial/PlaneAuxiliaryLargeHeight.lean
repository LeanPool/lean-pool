/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanPool.CCDN.Algebra.HomogeneousRankDichotomy
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryDegree
import LeanPool.CCDN.ForMathlib.Log

/-! The complementary large-coefficient-height auxiliary-degree estimate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Real

/-- Real bounds for the plane rank `s` with `2s + d² = d(2M + 3)` in the large-degree range
`32 d ≤ M`. -/
private lemma plane_rank_large_degree_bounds {s d M : ℕ} (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) :
    (0 : ℝ) < s ∧ (d : ℝ) * M ≤ 2 * s ∧ (s : ℝ) ≤ d * (M + 1) ∧ 16 * (d : ℝ) ^ 2 ≤ s := by
  have hdM : d ≤ M := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have he : 2 * (s : ℝ) + (d : ℝ) ^ 2 = d * (2 * M + 3) := by exact_mod_cast hr
  have hdMR : (d : ℝ) ≤ M := by exact_mod_cast hdM
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hslo : (d : ℝ) * M ≤ 2 * s := by nlinarith
  have hshi : (s : ℝ) ≤ d * (M + 1) := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hMlargeR : 32 * (d : ℝ) ≤ M := by exact_mod_cast hMlarge
  exact ⟨hsR, hslo, hshi, by nlinarith⟩

/-- Dividing the no-auxiliary comparison by `s² / 2` and bounding its archimedean error. -/
private lemma plane_comparison_div_le {s d M : ℕ} {B L K X : ℝ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
    (hcomparison : (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d - X - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log s - 4 * Real.log d - X - K ≤
      5 + 2 * M / s * Real.log B -
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have harch := plane_rank_archimedean_error hd hdM hr
  have hc : Real.log s - 4 * Real.log d - X - K ≤
      (Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) /
          ((s : ℝ) ^ 2 / 2) := (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 / 2 by positivity)).mpr
    (by simpa only [mul_comm] using hcomparison)
  calc
    _ ≤ _ := hc
    _ ≤ (5 * (s : ℝ) ^ 2 / 2 + s * M * Real.log B -
        (((2 + M).choose M : ℝ) - s) * Real.log L) / ((s : ℝ) ^ 2 / 2) := by
      gcongr
    _ = _ := by field_simp

/-- In the large-degree range, the box term is controlled by the coefficient height:
`(2M / s) log B ≤ (5/8) log H / d²` whenever `4 d log B ≤ log H`. -/
private lemma plane_box_term_le {s d M : ℕ} {B H : ℝ} (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) (hB : 1 ≤ B)
    (hheight : 4 * d * Real.log B ≤ Real.log H) :
    2 * (M : ℝ) / s * Real.log B ≤ 5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
  obtain ⟨hsR, hslo, -, -⟩ := plane_rank_large_degree_bounds hd hMlarge hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : 2 * (s : ℝ) + (d : ℝ) ^ 2 = d * (2 * M + 3) := by exact_mod_cast hr
  have hMlargeR : 32 * (d : ℝ) ≤ M := by exact_mod_cast hMlarge
  have hlogB := Real.log_nonneg hB
  have hboxrat : 2 * (M : ℝ) / s ≤ (5 / 2 : ℝ) / d := by
    apply (div_le_iff₀ hsR).mpr
    field_simp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hboxrat hlogB
  have hh' : (5 / 2 : ℝ) / d * Real.log B ≤ 5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
    field_simp
    nlinarith
  exact hh.trans hh'

/-- In the large-degree range, the coefficient term dominates the positioned height:
`(7/8)(log H / d² - T) ≤ 2 (binom(M + 2, 2) - s) / s² · log L` whenever
`log H ≤ log L + T d²`. -/
private lemma plane_coefficient_term_ge {s d M : ℕ} {L H T : ℝ} (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) (hL : 1 ≤ L)
    (hposition : Real.log H ≤ Real.log L + T * (d : ℝ) ^ 2) :
    7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
  obtain ⟨hsR, -, hshi, hslarge⟩ := plane_rank_large_degree_bounds hd hMlarge hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hsquare : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 2 * ((2 + M).choose M) := by
    have hsq := pow_le_pow_left₀ hsR.le hshi 2
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (show 0 ≤ (M : ℝ) + 1 by positivity)]
  have hlogL := Real.log_nonneg hL
  have hcoefrat : (7 / 8 : ℝ) / (d : ℝ) ^ 2 ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
    have hrat : 1 / (d : ℝ) ^ 2 - 2 / s ≤
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).mpr
      field_simp
      nlinarith
    have hrem : 2 / (s : ℝ) ≤ (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by
      apply (div_le_iff₀ hsR).mpr
      field_simp
      nlinarith
    have hid : (7 / 8 : ℝ) / (d : ℝ) ^ 2 =
        1 / (d : ℝ) ^ 2 - (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by ring
    linarith only [hrat, hrem, hid]
  have hh := mul_le_mul_of_nonneg_right hcoefrat hlogL
  have hh' : 7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
      (7 / 8 : ℝ) / (d : ℝ) ^ 2 * Real.log L := by
    field_simp
    nlinarith
  exact hh'.trans hh

/-- The plane rank satisfies `log d + log M - log 2 ≤ log s`, since `d M ≤ 2 s`. -/
private lemma plane_rank_log_ge {s d M : ℕ} (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) :
    Real.log d + Real.log M - Real.log 2 ≤ Real.log s := by
  obtain ⟨-, hslo, -, -⟩ := plane_rank_large_degree_bounds hd hMlarge hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h := Real.log_le_log (show (0 : ℝ) < d * M / 2 by positivity)
    (show (d : ℝ) * M / 2 ≤ s by linarith)
  rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hdR.ne' hMR.ne'] at h

/-- When the coefficient height exceeds B^(4d), a degree at least 32d
satisfying the no-auxiliary comparison is bounded by a constant times d³.
The constant includes the loss in positioning the leading coefficient. -/
theorem plane_auxiliary_large_height_log_bound {s d M : ℕ} {B L H T K : ℝ}
    (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log L + T * (d : ℝ) ^ 2)
    (hcomparison : (s : ℝ) ^ 2 / 2 *
        (Real.log s - 4 * Real.log d - Real.log (1 + Real.log H / (d : ℝ) ^ 2) - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d := by
  have hbasic := plane_comparison_div_le hd (by omega) hr hcomparison
  have hbox := plane_box_term_le hd hMlarge hr hB hheight
  have hcoef := plane_coefficient_term_ge (T := T) hd hMlarge hr hL hposition
  have hlogs := plane_rank_log_ge hd hMlarge hr
  have hlogA := Real.log_one_add_sub_div_four_le
    (show 0 ≤ Real.log H / (d : ℝ) ^ 2 by have := Real.log_nonneg hH; positivity)
  linarith

/-- Exponentiating the large-height logarithmic degree bound for plane curves: if
`log M ≤ K + 6 + log 2 + log 4 + T + 3 log d`, then `M ≤ 8 exp (K + 6 + T) d³`. -/
lemma plane_large_degree_bound_of_log_bound {d M : ℕ} {T K : ℝ}
    (hd : 0 < d) (hM : 0 < M)
    (hlog : Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d) :
    (M : ℝ) ≤ 8 * Real.exp (K + 6 + T) * (d : ℝ) ^ 3 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine Real.natCast_le_of_log_le_log hM (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
  have h8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  rw [h8]
  convert hlog using 1
  push_cast
  ring

end
end CCDN
