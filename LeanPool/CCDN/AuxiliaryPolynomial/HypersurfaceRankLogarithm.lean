/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! The logarithm of the exact hypersurface rank has the uniform leading
term log(d)+r*log(M), with an explicit error depending only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The dimension constant `r log 2 + log r! + r log (r + 1)` bounding the deviation of the
logarithm of the hypersurface Hilbert function from `log d + r log M`. -/
def hypersurfaceRankLogError (r : ℕ) : ℝ :=
  (r : ℝ) * Real.log 2 + Real.log (r.factorial : ℝ) + r * Real.log (r + 1 : ℝ)

/-- The rank logarithm loses only a dimension constant once M>=2d. -/
theorem hypersurface_rank_log_error {r d M s : ℕ} (hrpos : 0 < r) (hd : 0 < d)
    (hM : 2 * d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    |Real.log s - (Real.log d + (r : ℝ) * Real.log M)| ≤ hypersurfaceRankLogError r := by
  have hdM : d ≤ M := by omega
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs0 : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hdMR : 2 * (d : ℝ) ≤ M := by exact_mod_cast hM
  have hfac : (0 : ℝ) < r.factorial := by positivity
  obtain ⟨hl, hu⟩ := hypersurface_rank_power_bounds hdM hr
  have hl' : (d : ℝ) * ((M : ℝ) / 2) ^ r / (r.factorial : ℝ) ≤ s := by
    apply le_trans _ hl
    apply div_le_div_of_nonneg_right _ hfac.le
    apply mul_le_mul_of_nonneg_left _ hd0.le
    exact pow_le_pow_left₀ (by positivity) (by linarith) r
  have hu' : (s : ℝ) ≤ (d : ℝ) * (((r : ℝ) + 1) * M) ^ r / (r.factorial : ℝ) := by
    apply hu.trans
    apply div_le_div_of_nonneg_right _ hfac.le
    apply mul_le_mul_of_nonneg_left _ hd0.le
    apply pow_le_pow_left₀ (by positivity) _ r
    have hh := mul_le_mul_of_nonneg_left hM1 (Nat.cast_nonneg r)
    nlinarith
  have hlow :=
    Real.log_le_log (by positivity : (0 : ℝ) < (d : ℝ) * ((M : ℝ) / 2) ^ r / r.factorial) hl'
  rw [Real.log_div (by positivity) hfac.ne', Real.log_mul hd0.ne' (by positivity),
    Real.log_pow, Real.log_div hM0.ne' (by norm_num)] at hlow
  have hhigh := Real.log_le_log hs0 hu'
  rw [Real.log_div (by positivity) hfac.ne', Real.log_mul hd0.ne' (by positivity),
    Real.log_pow, Real.log_mul (by positivity) hM0.ne'] at hhigh
  have hlogfac : 0 ≤ Real.log (r.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.factorial_pos r)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogr : 0 ≤ Real.log (r + 1 : ℝ) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  unfold hypersurfaceRankLogError
  apply abs_le.mpr
  constructor <;>
    nlinarith [mul_nonneg (Nat.cast_nonneg r) hlog2, mul_nonneg (Nat.cast_nonneg r) hlogr]

end
end CCDN
