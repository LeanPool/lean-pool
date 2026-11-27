/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The series `∑ (n+1)³ 2⁻ⁿ = 52`

The numerical identity used in the proof of Theorem 7.2 of the manuscript (the display
before `eq:J0`, (7.14)).
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Partial sums: `∑_{n<N} (n+1)³ 2⁻ⁿ = 52 - (2N³ + 12N² + 36N + 52) 2⁻ᴺ`. -/
theorem sum_range_cube_mul_half_pow (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n
      = 52 - (2 * (N : ℝ) ^ 3 + 12 * (N : ℝ) ^ 2 + 36 * (N : ℝ) + 52) * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- `∑_{n ≥ 0} (n+1)³ 2⁻ⁿ = 52`. -/
theorem hasSum_cube_mul_half_pow :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n) 52 := by
  have hnonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n := fun n => by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hr : |(1 / 2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have h3 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 3 hr
  have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hr
  have hlim := (tendsto_const_nhds (x := (52 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
    ((((h3.const_mul 2).add (h2.const_mul 12)).add (h1.const_mul 36)).add (h0.const_mul 52))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  refine hlim.congr (fun N => ?_)
  rw [sum_range_cube_mul_half_pow]
  ring

end VacuumBellSeparation
