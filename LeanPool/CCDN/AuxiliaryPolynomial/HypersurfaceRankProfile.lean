/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-! Uniform bounds for the exact homogeneous hypersurface Hilbert rank.
The factorial leading coefficient is retained in both directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset

private lemma sum_shifted_choose_add (r k d : ℕ) :
    (∑ i ∈ range d, (r + 1 + k + i).choose r) + (r + 1 + k).choose (r + 1) =
      (r + 1 + k + d).choose (r + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hp := Nat.choose_succ_succ' (r + 1 + k + d) r
    rw [show r + 1 + k + (d + 1) = (r + 1 + k + d) + 1 by omega]
    omega

/-- The exact rank is a sum of d adjacent binomial layers. -/
private theorem hypersurface_rank_eq_sum {r d M s : ℕ} (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    s = ∑ i ∈ range d, (r + 1 + (M - d) + i).choose r := by
  have hh := sum_shifted_choose_add r (M - d) d
  rw [show r + 1 + (M - d) + d = r + 1 + M by omega] at hh
  rw [← Nat.choose_symm_add (a := r + 1) (b := M - d),
    ← Nat.choose_symm_add (a := r + 1) (b := M)] at hr
  omega

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables,
given by `s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, satisfies
`d * C(r + (M - d), r) ≤ s ≤ d * C(r + M, r)`. -/
lemma hypersurface_rank_binomial_bounds {r d M s : ℕ} (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    d * (r + (M - d)).choose r ≤ s ∧ s ≤ d * (r + M).choose r := by
  rw [hypersurface_rank_eq_sum hdM hr]
  constructor
  · calc
      _ = ∑ _i ∈ range d, (r + (M - d)).choose r := by simp
      _ ≤ _ := sum_le_sum fun i _ => Nat.choose_le_choose r (by omega)
  · calc
      _ ≤ ∑ _i ∈ range d, (r + M).choose r :=
        sum_le_sum fun i hi => Nat.choose_le_choose r (by have := mem_range.mp hi; omega)
      _ = _ := by simp

/-- Uniform power bounds with exact leading coefficient d/r!.
The error is controlled by shifts of at most d and r in the degree M. -/
theorem hypersurface_rank_power_bounds {r d M s : ℕ} (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    (d : ℝ) * ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ s ∧
      (s : ℝ) ≤ (d : ℝ) * ((M : ℝ) + r) ^ r / (r.factorial : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hloR : (d : ℝ) * ((r + (M - d)).choose r : ℝ) ≤ s := by exact_mod_cast hlo
  have hhiR : (s : ℝ) ≤ (d : ℝ) * ((r + M).choose r : ℝ) := by exact_mod_cast hhi
  have hl : ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ (r + (M - d)).choose r := by
    have h := Nat.pow_le_choose (α := ℝ) r (r + (M - d))
    rw [show r + (M - d) + 1 - r = M - d + 1 by omega] at h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hdM] using h
  have hu : ((r + M).choose r : ℝ) ≤ ((M : ℝ) + r) ^ r / (r.factorial : ℝ) := by
    simpa only [Nat.cast_add, add_comm] using Nat.choose_le_pow_div (α := ℝ) r (r + M)
  constructor
  · have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)
    rw [← mul_div_assoc] at h
    exact h.trans hloR
  · exact hhiR.trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg d))

end
end CCDN
