/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.SimplexMatrices
public import LeanPool.NoncommutativeAMGM.SimplexRecurrence

/-! # The two scalar coefficients of a distinct-index simplex product -/

@[expose] public section

namespace NoncommutativeAMGM

/-- Axis coefficient and total simplex coefficient after `k` fresh factors. -/
noncomputable def simplexTransfer (d α β : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 =>
    let v := simplexTransfer d α β k
    (v.1 - (β / d) * v.2, β * v.1 + (α - (β ^ 2 - α) / d) * v.2)

/-- Elimination of the second coordinate gives the Appendix A recurrence. -/
theorem simplexTransfer_recurrence {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1) (k : ℕ) :
    (simplexTransfer ((n : ℝ) - 1) α β (k + 2)).1 =
      (2 * α) * (simplexTransfer ((n : ℝ) - 1) α β (k + 1)).1 -
        (α * (n : ℝ) / ((n : ℝ) - 1)) *
          (simplexTransfer ((n : ℝ) - 1) α β k).1 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  have hδ : α - (β ^ 2 - α) / ((n : ℝ) - 1) = 2 * α - 1 := by
    field_simp
    nlinarith [hαβ]
  have hβ : 1 - β / ((n : ℝ) - 1) * β =
      2 * α - α * (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp
    nlinarith [hαβ]
  simp only [simplexTransfer, hδ]
  calc
    _ = (1 - β / ((n : ℝ) - 1) * β) *
          (simplexTransfer ((n : ℝ) - 1) α β k).1 -
        2 * α * (β / ((n : ℝ) - 1)) *
          (simplexTransfer ((n : ℝ) - 1) α β k).2 := by ring
    _ = _ := by rw [hβ]; ring

/-- The transfer iteration is identified with the recursively defined scalar sequence. -/
theorem simplexTransfer_fst {n : ℕ} (hn : 1 < n) (α β : ℝ)
    (hαβ : ((n : ℝ) - 2) * α + β ^ 2 = (n : ℝ) - 1) (k : ℕ) :
    (simplexTransfer ((n : ℝ) - 1) α β k).1 =
      simplexRecurrence (2 * α) (α * (n : ℝ) / ((n : ℝ) - 1)) k := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [simplexTransfer]
  | more k hk hk1 =>
    rw [simplexTransfer_recurrence hn α β hαβ, hk1, hk, simplexRecurrence_step]

end NoncommutativeAMGM
