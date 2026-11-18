/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Scalar spectral multipliers for a positive contraction resolvent

These reusable scalar lemmas are ingredients for the full weak-form semigroup.
They do not themselves identify any concrete diffusion operator.
-/

@[expose] public section

open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Time evolution expressed through a resolvent spectral coordinate. -/
def resolventEvolutionMultiplier (t r : ℝ) : ℝ :=
  if t = 0 then 1 else Real.exp t * expNegInvGlue (r / t)

@[simp] theorem resolventEvolutionMultiplier_zero (r : ℝ) :
    resolventEvolutionMultiplier 0 r = 1 := by simp [resolventEvolutionMultiplier]

theorem resolventEvolutionMultiplier_continuous (t : ℝ) :
    Continuous (resolventEvolutionMultiplier t) := by
  unfold resolventEvolutionMultiplier
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul (((expNegInvGlue.contDiff : ContDiff ℝ ∞
    expNegInvGlue).continuous).comp (continuous_id.div_const t))

theorem resolventEvolutionMultiplier_positive_formula {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    resolventEvolutionMultiplier t r = Real.exp (-t * (r⁻¹ - 1)) := by
  rw [resolventEvolutionMultiplier, ite_eq_right ht.ne', expNegInvGlue,
    ite_eq_right (not_le.mpr (div_pos hr ht)), ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem resolventEvolutionMultiplier_nonpositive {t r : ℝ} (ht : 0 < t) (hr : r ≤ 0) :
    resolventEvolutionMultiplier t r = 0 := by
  rw [resolventEvolutionMultiplier, ite_eq_right ht.ne', expNegInvGlue.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg hr ht.le), mul_zero]

/-- Exact scalar semigroup law at all nonnegative times. -/
theorem resolventEvolutionMultiplier_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (r : ℝ) :
    resolventEvolutionMultiplier (s + t) r =
      resolventEvolutionMultiplier s r * resolventEvolutionMultiplier t r := by
  by_cases hs0 : s = 0
  · subst s; simp
  by_cases ht0 : t = 0
  · subst t; simp
  have hspos := lt_of_le_of_ne hs (Ne.symm hs0)
  have htpos := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hr : 0 < r
  · rw [resolventEvolutionMultiplier_positive_formula (add_pos hspos htpos) hr,
      resolventEvolutionMultiplier_positive_formula hspos hr,
      resolventEvolutionMultiplier_positive_formula htpos hr, ← Real.exp_add]
    congr 1
    ring
  · rw [resolventEvolutionMultiplier_nonpositive (add_pos hspos htpos) (le_of_not_gt hr),
      resolventEvolutionMultiplier_nonpositive hspos (le_of_not_gt hr), zero_mul]

/-- Contractive multiplier on the spectrum of a positive contraction. -/
theorem resolventEvolutionMultiplier_mem_unit_interval {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    resolventEvolutionMultiplier t r ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ht0 : t = 0
  · subst t; simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hr0 : r = 0
  · subst r
    rw [resolventEvolutionMultiplier_nonpositive htpos le_rfl]
    simp
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  rw [resolventEvolutionMultiplier_positive_formula htpos hrpos]
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hrpos).mpr hr.2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sub_nonneg.mpr hinv)

/-- The uniform range estimate that gives strong continuity at zero even
when zero belongs to the resolvent spectrum. -/
theorem resolventEvolutionMultiplier_range_error {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |(resolventEvolutionMultiplier t r - 1) * r| ≤ t := by
  by_cases ht0 : t = 0
  · subst t; simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hr0 : r = 0
  · subst r; simpa using ht
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hbounds := resolventEvolutionMultiplier_mem_unit_interval ht hr
  have habs : |(resolventEvolutionMultiplier t r - 1) * r| =
      (1 - resolventEvolutionMultiplier t r) * r := by
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbounds.2) hr.1)]
    ring
  rw [habs, resolventEvolutionMultiplier_positive_formula htpos hrpos]
  have he := Real.add_one_le_exp (-t * (r⁻¹ - 1))
  have he' : 1 - Real.exp (-t * (r⁻¹ - 1)) ≤ t * (r⁻¹ - 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_right he' hr.1
  have hc : t * (r⁻¹ - 1) * r = t * (1 - r) := by
    field_simp
  rw [hc] at hmul
  exact hmul.trans (by nlinarith [hr.1])

/-- A global second-order bound on the negative exponential remainder. -/
theorem exp_neg_remainder_le_sq {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x) - 1 + x| ≤ x ^ 2 := by
  by_cases hsmall : x ≤ 1
  · have he := Real.abs_exp_sub_one_sub_id_le
      (x := -x) (by simpa only [abs_neg, abs_of_nonneg hx] using hsmall)
    simpa only [sub_neg_eq_add, neg_sq] using he
  · have hlow := Real.add_one_le_exp (-x)
    have hupp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- Uniform quadratic error on the twice-resolved range. -/
theorem resolventEvolutionMultiplier_second_error {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |(resolventEvolutionMultiplier t r - 1) * r ^ 2 - t * (r ^ 2 - r)| ≤ t ^ 2 := by
  by_cases ht0 : t = 0
  · subst t; simp
  have htpos := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hr0 : r = 0
  · subst r; simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self, abs_zero]
    exact sq_nonneg t
  have hrpos := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hrpos).mpr hr.2
  have he := exp_neg_remainder_le_sq (mul_nonneg ht (sub_nonneg.mpr hinv))
  have he' := mul_le_mul_of_nonneg_right he (sq_nonneg r)
  rw [resolventEvolutionMultiplier_positive_formula htpos hrpos]
  have harg : (Real.exp (-t * (r⁻¹ - 1)) - 1) * r ^ 2 - t * (r ^ 2 - r) =
      (Real.exp (-(t * (r⁻¹ - 1))) - 1 + t * (r⁻¹ - 1)) * r ^ 2 := by
    rw [neg_mul]
    field_simp
    ring
  rw [harg, abs_mul, abs_of_nonneg (sq_nonneg r)]
  apply he'.trans
  have hid : (t * (r⁻¹ - 1)) ^ 2 * r ^ 2 = t ^ 2 * (1 - r) ^ 2 := by
    field_simp
  rw [hid]
  apply mul_le_of_le_one_right (sq_nonneg t)
  nlinarith [hr.1, hr.2]

end
end GinibrePoincare
