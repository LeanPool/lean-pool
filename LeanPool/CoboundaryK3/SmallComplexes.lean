/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import LeanPool.CoboundaryK3.Witnesses

/-!
# `h₁(K_k) = k/3` for `4 ≤ k ≤ 8` from the explicit witnesses

Theorem 4 of the paper. Each witness of Appendix A has gauge distance exactly `D`
(`gaugeDist_w4`, …, `gaugeDist_w8`), so it bounds the constant from above by `N/D = k/3`
(`h1_le_k4`, …, `h1_le_k8`), and the star-gauge lower bound `k_div_three_le_h1` of `Constant`
closes the gap (`h1_eq_k4`, …, `h1_eq_k8`, `h1_eq_k_div_three`).

These values are also special cases of `h1_eq_all` in `Staircase`, which does not use the
`k = 6, 7, 8` witnesses; this file records that the explicit cochains of Appendix A attain them.
-/

@[expose] public section

namespace CoboundaryK3

open Equiv

variable {k : ℕ}

/-! ## The upper bound from the witnesses -/

/-- The `k = 4` witness has gauge distance exactly `6`. -/
theorem gaugeDist_w4 : gaugeDist w4 = 6 := gaugeDist_eq_of witness_k4.2.1 _ witness_k4.2.2.1

/-- The `k = 5` witness has gauge distance exactly `6`. -/
theorem gaugeDist_w5 : gaugeDist w5 = 6 := gaugeDist_eq_of witness_k5.2.1 _ witness_k5.2.2.1

/-- The `k = 6` witness has gauge distance exactly `18`. -/
theorem gaugeDist_w6 : gaugeDist w6 = 18 := gaugeDist_eq_of witness_k6.2.1 _ witness_k6.2.2.1

/-- The `k = 7` witness has gauge distance exactly `12`. -/
theorem gaugeDist_w7 : gaugeDist w7 = 12 := gaugeDist_eq_of witness_k7.2.1 _ witness_k7.2.2.1

/-- The `k = 8` witness has gauge distance exactly `27`. -/
theorem gaugeDist_w8 : gaugeDist w8 = 27 := gaugeDist_eq_of witness_k8.2.1 _ witness_k8.2.2.1

/-- **Theorem 4, upper half, k = 4.** `h₁(K_4) ≤ 4/3`, from the witness `w4` (`N = 8`,
`D = 6`). -/
theorem h1_le_k4 : h1 4 ≤ 4 / 3 := by
  have h := h1_le_of_pos (α := w4) (by rw [gaugeDist_w4]; all_goals norm_num)
  rw [gaugeDist_w4, witness_k4.1] at h
  calc h1 4 ≤ ((8 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) := h
    _ = 4 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 5.** `h₁(K_5) ≤ 5/3`, from the witness `w5` (`N = 10`,
`D = 6`). -/
theorem h1_le_k5 : h1 5 ≤ 5 / 3 := by
  have h := h1_le_of_pos (α := w5) (by rw [gaugeDist_w5]; all_goals norm_num)
  rw [gaugeDist_w5, witness_k5.1] at h
  calc h1 5 ≤ ((10 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) := h
    _ = 5 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 6.** `h₁(K_6) ≤ 6/3`, from the witness `w6` (`N = 36`,
`D = 18`). -/
theorem h1_le_k6 : h1 6 ≤ 6 / 3 := by
  have h := h1_le_of_pos (α := w6) (by rw [gaugeDist_w6]; all_goals norm_num)
  rw [gaugeDist_w6, witness_k6.1] at h
  calc h1 6 ≤ ((36 : ℕ) : ℝ) / ((18 : ℕ) : ℝ) := h
    _ = 6 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 7.** `h₁(K_7) ≤ 7/3`, from the witness `w7` (`N = 28`,
`D = 12`). -/
theorem h1_le_k7 : h1 7 ≤ 7 / 3 := by
  have h := h1_le_of_pos (α := w7) (by rw [gaugeDist_w7]; all_goals norm_num)
  rw [gaugeDist_w7, witness_k7.1] at h
  calc h1 7 ≤ ((28 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) := h
    _ = 7 / 3 := by norm_num

/-- **Theorem 4, upper half, k = 8.** `h₁(K_8) ≤ 8/3`, from the witness `w8` (`N = 72`,
`D = 27`). -/
theorem h1_le_k8 : h1 8 ≤ 8 / 3 := by
  have h := h1_le_of_pos (α := w8) (by rw [gaugeDist_w8]; all_goals norm_num)
  rw [gaugeDist_w8, witness_k8.1] at h
  calc h1 8 ≤ ((72 : ℕ) : ℝ) / ((27 : ℕ) : ℝ) := h
    _ = 8 / 3 := by norm_num


/-! ## The value: `h₁(K_k) = k/3` for `4 ≤ k ≤ 8` -/

/-- **Theorem 4, k = 4.** `h₁(K_4) = 4/3`. -/
theorem h1_eq_k4 : h1 4 = 4 / 3 := by
  apply le_antisymm h1_le_k4
  have h := k_div_three_le_h1 (k := 4) ⟨w4, by rw [gaugeDist_w4]; all_goals norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 5.** `h₁(K_5) = 5/3`. -/
theorem h1_eq_k5 : h1 5 = 5 / 3 := by
  apply le_antisymm h1_le_k5
  have h := k_div_three_le_h1 (k := 5) ⟨w5, by rw [gaugeDist_w5]; all_goals norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 6.** `h₁(K_6) = 6/3 = 2`. -/
theorem h1_eq_k6 : h1 6 = 6 / 3 := by
  apply le_antisymm h1_le_k6
  have h := k_div_three_le_h1 (k := 6) ⟨w6, by rw [gaugeDist_w6]; all_goals norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 7.** `h₁(K_7) = 7/3`. -/
theorem h1_eq_k7 : h1 7 = 7 / 3 := by
  apply le_antisymm h1_le_k7
  have h := k_div_three_le_h1 (k := 7) ⟨w7, by rw [gaugeDist_w7]; all_goals norm_num⟩
  exact_mod_cast h

/-- **Theorem 4, k = 8.** `h₁(K_8) = 8/3`. -/
theorem h1_eq_k8 : h1 8 = 8 / 3 := by
  apply le_antisymm h1_le_k8
  have h := k_div_three_le_h1 (k := 8) ⟨w8, by rw [gaugeDist_w8]; all_goals norm_num⟩
  exact_mod_cast h

/-- **Theorem 4.** `h₁(K_k) = k/3` for `k = 4, 5, 6, 7, 8`. -/
theorem h1_eq_k_div_three : ∀ k ∈ ({4, 5, 6, 7, 8} : Finset ℕ), h1 k = (k : ℝ) / 3 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · rw [h1_eq_k4]; all_goals norm_num
  · rw [h1_eq_k5]; all_goals norm_num
  · rw [h1_eq_k6]; all_goals norm_num
  · rw [h1_eq_k7]; all_goals norm_num
  · rw [h1_eq_k8]; all_goals norm_num

end CoboundaryK3
