/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SineNodeBounds

/-! # The squared sine margin at each interior Chebyshev extremum -/

@[expose] public section

namespace NoncommutativeAMGM

/-- Jordan's inequality gives the exact quadratic margin on the first half-grid. -/
theorem chebyshevNode_margin_first_half {m j : ℕ} (hm : 0 < m) (hj : 2 * j ≤ m) :
    4 / (m : ℝ) ^ 2 * (j : ℝ) ^ 2 ≤ 1 - chebyshevNode m j ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj' : 2 * (j : ℝ) ≤ m := by exact_mod_cast hj
  have hθ : (j : ℝ) * Real.pi / m ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hm').mpr
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin (show 0 ≤ (j : ℝ) * Real.pi / m by positivity) hθ
  have he : 2 / Real.pi * ((j : ℝ) * Real.pi / m) = 2 * (j : ℝ) / m := by
    field_simp
  rw [he] at hs
  have hsq := mul_self_le_mul_self (show 0 ≤ 2 * (j : ℝ) / m by positivity) hs
  have hn : (2 * (j : ℝ) / m) * (2 * (j : ℝ) / m) =
      4 / (m : ℝ) ^ 2 * (j : ℝ) ^ 2 := by ring
  rw [hn] at hsq
  have hi := Real.sin_sq_add_cos_sq ((j : ℝ) * Real.pi / m)
  change _ ≤ 1 - Real.cos ((j : ℝ) * Real.pi / m) ^ 2
  nlinarith

/-- The distance to the nearer endpoint controls the squared sine margin. -/
theorem chebyshevNode_margin {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    4 / (m : ℝ) ^ 2 * (min j (m - j) : ℕ) ^ 2 ≤ 1 - chebyshevNode m j ^ 2 := by
  by_cases h : j ≤ m - j
  · rw [min_eq_left h]
    exact chebyshevNode_margin_first_half hm (by omega)
  · rw [min_eq_right (by omega : m - j ≤ j)]
    have he := chebyshevNode_margin_first_half (j := m - j) hm (by omega)
    rw [chebyshevNode_complement hm hj, neg_sq] at he
    exact he

/-- Every interior extremum has squared sine at least `4/m²`. -/
theorem chebyshevNode_margin_interior {m j : ℕ} (hm : 0 < m) (hj0 : 0 < j) (hjm : j < m) :
    4 / (m : ℝ) ^ 2 ≤ 1 - chebyshevNode m j ^ 2 := by
  have hk : (1 : ℝ) ≤ (min j (m - j) : ℕ) := by
    exact_mod_cast (show 1 ≤ min j (m - j) by omega)
  have hsq : (1 : ℝ) ≤ ((min j (m - j) : ℕ) : ℝ) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 / (m : ℝ) ^ 2 by positivity)
  simpa only [mul_one] using h.trans (chebyshevNode_margin hm hjm.le)

end NoncommutativeAMGM
