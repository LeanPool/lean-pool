/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! The factorial and coefficient-count logarithms in the determinant
comparison cost only a dimension constant times s^(1+1/r). -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables, given by
`s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, is at least `M` when `0 < r` and
`0 < d ≤ M`. -/
lemma hypersurface_rank_ge_degree_parameter {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) : M ≤ s := by
  have hc : M - d + 1 ≤ (r + (M - d)).choose r := by
    calc
      _ = (M - d + 1).choose (M - d) := (Nat.choose_succ_self_right _).symm
      _ ≤ (r + (M - d)).choose (M - d) := Nat.choose_le_choose _ (by omega)
      _ = _ := Nat.choose_symm_add.symm
  have hl := (Nat.mul_le_mul_left d hc).trans (hypersurface_rank_binomial_bounds hdM hr).1
  have hk := Nat.mul_le_mul_right (M - d) (show 1 ≤ d from hd)
  have he := Nat.sub_add_cancel hdM
  nlinarith

/-- For `0 < r` and positive real `s`, `log s ≤ r * s ^ (1/r)`. -/
lemma log_le_dimension_root {r : ℕ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    Real.log s ≤ (r : ℝ) * s ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hh := Real.log_le_self (Real.rpow_nonneg hs.le (1 / (r : ℝ)))
  rw [Real.log_rpow hs] at hh
  have hm := mul_le_mul_of_nonneg_left hh hr0.le
  have he : (r : ℝ) * ((1 / (r : ℝ)) * Real.log s) = Real.log s := by field_simp
  rwa [he] at hm

/-- The coefficient count is polynomial in rank, with explicit dimension. -/
private lemma hypersurface_rank_log_dimension_bound {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    Real.log ((r + 1 + M).choose M : ℝ) ≤ (r + 1 : ℝ) * (Real.log 2 + Real.log s) := by
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have hdim : (r + 1 + M).choose M ≤ (M + 1) ^ (r + 1) := by
    rw [← Nat.choose_symm_add (a := r + 1) (b := M), Nat.add_comm (r + 1) M]
    exact Nat.choose_add_le_add_one_pow M (r + 1)
  have hdimR : ((r + 1 + M).choose M : ℝ) ≤ ((M : ℝ) + 1) ^ (r + 1) := by exact_mod_cast hdim
  have hMsR : (M : ℝ) ≤ s := by exact_mod_cast hMs
  have hbound : ((r + 1 + M).choose M : ℝ) ≤ (2 * (s : ℝ)) ^ (r + 1) :=
    hdimR.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hpos : (0 : ℝ) < (r + 1 + M).choose M := by
    exact_mod_cast Nat.choose_pos (by omega : M ≤ r + 1 + M)
  have hh := Real.log_le_log hpos hbound
  rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith : (s : ℝ) ≠ 0)] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- The dimension constant `((r + 2) r + (r + 1)) / 2` bounding the archimedean logarithmic
terms of the determinant comparison by a multiple of `s ^ (1 + 1/r)`. -/
def hypersurfaceArchimedeanError (r : ℕ) : ℝ := ((r + 2 : ℝ) * r + (r + 1 : ℝ)) / 2

/-- The two archimedean logarithmic terms have the exact scale of the main
rank term and cost only an explicit dimension constant. -/
theorem hypersurface_rank_archimedean_error {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((r + 1 + M).choose M : ℝ) ≤
      hypersurfaceArchimedeanError r * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log s := by
    have hh : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hh
  have hlog := hypersurface_rank_log_dimension_bound hrpos hd hdM hr
  have hlroot := log_le_dimension_root hrpos hs0
  have hroot1 : 1 ≤ (s : ℝ) ^ (1 / (r : ℝ)) := Real.one_le_rpow hs1 (by positivity)
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hdim : Real.log ((r + 1 + M).choose M : ℝ) ≤
      (r + 1 : ℝ) * ((r + 1 : ℝ) * (s : ℝ) ^ (1 / (r : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left hlroot (show 0 ≤ (r + 1 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hl2.trans hroot1) (show 0 ≤ (r + 1 : ℝ) by positivity)
    nlinarith
  have hfac := mul_le_mul_of_nonneg_left hlroot hs0.le
  have hdim' := mul_le_mul_of_nonneg_left hdim (show 0 ≤ (s : ℝ) / 2 by positivity)
  rw [Real.rpow_add hs0, Real.rpow_one]
  unfold hypersurfaceArchimedeanError
  nlinarith

end
end CCDN
