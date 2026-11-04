/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.ClosedFormHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The integer minor has the logarithmic height needed by the
fourth-power prime cutoff. The charge applies to primes with proved matrix
rank drop; identifying these with the geometric bad primes is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix Real

private lemma log_factorial_le_square (r : ℕ) : Real.log (r.factorial : ℝ) ≤ (r : ℝ) ^ 2 := by
  by_cases hr : r = 0
  · simp [hr]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hh : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < r.factorial) hh
  rw [Real.log_pow] at hl
  exact hl.trans (by nlinarith [Real.log_le_self hr0.le])

/-- The determinant height fits the cutoff L=27*d^4 with scaled
height 1+log(H)/d². -/
theorem closedForm_minor_log_height
    (d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ 2 * d ^ 2)
    (f : ℤ[X][X]) (H : ℝ) (hH : 1 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d)
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d)
    (hD : ((closedFormCoefficientMatrix d f).submatrix a c).det ≠ 0) :
    Real.log |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr' : (r : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by exact_mod_cast hr
  have hH0 : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg hH
  have hE0 : 0 < 2 * (d : ℝ) * H := by positivity
  have hb := closedForm_integer_minor_bound d r f H hH0.le hf houter hinner a c
  have hD0 : (0 : ℝ) < |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr hD)
  have hl := Real.log_le_log hD0 hb
  rw [Real.log_mul (by positivity : (r.factorial : ℝ) ≠ 0) (pow_ne_zero _ hE0.ne'),
    Real.log_pow, Real.log_mul (by positivity : 2 * (d : ℝ) ≠ 0) hH0.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hd0.ne'] at hl
  have hfac := log_factorial_le_square r
  have hl2 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
  have hld := Real.log_le_self hd0.le
  have hterm : (r : ℝ) * (Real.log 2 + Real.log d + Real.log H) ≤
      2 * (d : ℝ) ^ 2 * (2 + d + Real.log H) := by
    calc
      _ ≤ (r : ℝ) * (2 + d + Real.log H) := mul_le_mul_of_nonneg_left (by linarith) hr0
      _ ≤ _ := mul_le_mul_of_nonneg_right hr' (by positivity)
  have hrsq : (r : ℝ) ^ 2 ≤ (2 * (d : ℝ) ^ 2) ^ 2 := by nlinarith
  have hd2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have hd3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) ^ 3 by positivity) (sub_nonneg.mpr hd1)]
  have he : (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) =
      27 * (d : ℝ) ^ 4 + 27 * (d : ℝ) ^ 2 * Real.log H := by
    field_simp
  rw [he]
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) hlog]

end
end CCDN
