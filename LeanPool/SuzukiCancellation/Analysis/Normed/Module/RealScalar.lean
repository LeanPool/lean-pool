/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Ring

/-!
# Norm bounds for real scalar multiples

Bounds use only the real scalar norm; no exponential construction is required.

## Main results

* `TrotterError.norm_smul_le_of_abs_le_one`.
* `TrotterError.norm_smul_exp_arg_le`.
-/

@[expose] public section

namespace TrotterError

/-- A scalar of absolute value at most one does not increase the seminorm. -/
lemma norm_smul_le_of_abs_le_one {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (A : E) (hc : |c| ≤ 1) : ‖c • A‖ ≤ ‖A‖ := by
  calc
    ‖c • A‖ = |c| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖A‖ := one_mul _

/-- For `u ≤ 1`, `0 ≤ t`, and `|c| ≤ 1`, the scaled seminorm `(u * t) * ‖c • A‖` is at
most `t * ‖A‖`. -/
lemma norm_smul_exp_arg_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (A : E) (hc : |c| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu1 : u ≤ 1) :
    (u * t) * ‖c • A‖ ≤ t * ‖A‖ := by
  have hc' : u * |c| ≤ 1 := by
    simpa using mul_le_mul hu1 hc (abs_nonneg _) zero_le_one
  have hle : u * t * |c| ≤ t := by
    calc
      u * t * |c| = t * (u * |c|) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hc' ht
      _ = t := mul_one _
  calc
    (u * t) * ‖c • A‖ = u * t * |c| * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ t * ‖A‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

end TrotterError
