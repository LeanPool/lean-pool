/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Projection.DegreePreservingProjectionBox
public import LeanPool.CCDN.Statements
import LeanPool.CCDN.ForMathlib.Log

/-! Absorb the degree-dependent projection box factor into a constant depending
only on ambient dimension, retaining the exact exponent 1/d and d³ factor. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The constant `c = 2 * n ^ 2 + 3 * n`, for which `log (projectionBoxFactor n d) ≤ c * d`. -/
def projectionLogConstant (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 + 3 * n

/-- The projection log constant is nonnegative. -/
lemma projectionLogConstant_nonneg (n : ℕ) : 0 ≤ projectionLogConstant n := by
  unfold projectionLogConstant
  positivity

/-- For `d > 0`, the logarithm of the projection box factor is at most
`projectionLogConstant n * d`. -/
lemma projectionBoxFactor_log_le (n : ℕ) {d : ℕ} (hd : 0 < d) :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  have hln : Real.log ((n : ℝ) + 1) ≤ n := Real.log_add_one_le_self hn
  have hld : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  unfold projectionBoxFactor
  rw [Real.log_mul hn0.ne' (pow_pos (pow_pos (mul_pos hn0 hd0) _) _).ne',
    Real.log_pow, Real.log_pow, Real.log_mul hn0.ne' hd0.ne']
  unfold projectionLogConstant
  have hh := mul_le_mul_of_nonneg_left (add_le_add hln hld) (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hh₂ := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ 2 * (n : ℝ) ^ 2 + n by positivity)
  norm_num only [Nat.cast_ofNat]
  nlinarith

private lemma curveBound_scale_of_log_le {d : ℕ} (hd : 0 < d) {A B C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hlog : Real.log A ≤ C * d) :
    curveBound d (A * B) ≤ Real.exp C * (C + 1) * curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogA := Real.log_nonneg hA
  have hpow : A ^ (1 / (d : ℝ)) ≤ Real.exp C := by
    rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ hd0).mpr hlog
  have hlog₂ : Real.log A + Real.log B + d ≤ (C + 1) * (Real.log B + d) := by
    nlinarith [mul_nonneg hC hlogB]
  unfold curveBound
  rw [Real.mul_rpow hA0.le hB0.le, Real.log_mul hA0.ne' hB0.ne']
  calc
    _ ≤ (d : ℝ) ^ 3 * (Real.exp C * B ^ (1 / (d : ℝ))) *
        ((C + 1) * (Real.log B + d)) := by gcongr
    _ = _ := by ring

/-- Scaling the radius by the projection box factor multiplies the curve bound by at most a
constant depending only on `n`: with `c = projectionLogConstant n`, for `d > 0` and `B ≥ 1`,
`curveBound d (projectionBoxFactor n d * B) ≤ exp c * (c + 1) * curveBound d B`. -/
theorem projection_curveBound_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (projectionBoxFactor n d * B) ≤
      (Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)) * curveBound d B :=
  curveBound_scale_of_log_le hd (projectionBoxFactor_one_le n d) hB
    (projectionLogConstant_nonneg n) (projectionBoxFactor_log_le n hd)

end
end CCDN
