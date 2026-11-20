/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.CosineGap

/-! # The rounded Chebyshev slice nodes and their strict separation -/

@[expose] public section
namespace NoncommutativeAMGM

/-- The unrounded slice coordinate at a Chebyshev extremum. -/
noncomputable def idealSliceNode (n m j : ℕ) : ℝ := (n : ℝ) / 2 * (1 - chebyshevNode m j)

/-- Nearest-integer rounding, with the convention from equation (23). -/
noncomputable def roundedSliceNode (n m j : ℕ) : ℕ := ⌊(1 / 2 : ℝ) + idealSliceNode n m j⌋₊

theorem idealSliceNode_nonneg (n m j : ℕ) : 0 ≤ idealSliceNode n m j :=
  mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))

theorem idealSliceNode_le (n m j : ℕ) : idealSliceNode n m j ≤ n := by
  calc
    _ ≤ (n : ℝ) / 2 * 2 := mul_le_mul_of_nonneg_left
      (by have hc : -1 ≤ chebyshevNode m j := Real.neg_one_le_cos _; linarith)
      (by positivity)
    _ = _ := by ring

theorem roundedSliceNode_band (n m j : ℕ) :
    idealSliceNode n m j - 1 / 2 < (roundedSliceNode n m j : ℝ) ∧
      (roundedSliceNode n m j : ℝ) ≤ idealSliceNode n m j + 1 / 2 := by
  have hpos : 0 ≤ (1 / 2 : ℝ) + idealSliceNode n m j := by
    linarith [idealSliceNode_nonneg n m j]
  have hlo := Nat.lt_floor_add_one ((1 / 2 : ℝ) + idealSliceNode n m j)
  have hhi := Nat.floor_le hpos
  change _ < (roundedSliceNode n m j : ℝ) + 1 at hlo
  change (roundedSliceNode n m j : ℝ) ≤ _ at hhi
  constructor <;> linarith

theorem roundedSliceNode_error (n m j : ℕ) :
    |(roundedSliceNode n m j : ℝ) - idealSliceNode n m j| ≤ 1 / 2 := by
  have h := roundedSliceNode_band n m j
  rw [abs_le]
  constructor <;> linarith

theorem roundedSliceNode_le (n m j : ℕ) : roundedSliceNode n m j ≤ n := by
  have h := roundedSliceNode_band n m j
  have hle := idealSliceNode_le n m j
  have hlt : (roundedSliceNode n m j : ℝ) < (n : ℝ) + 1 := by linarith
  have : roundedSliceNode n m j < n + 1 := by exact_mod_cast hlt
  omega

@[simp] theorem roundedSliceNode_zero (n m : ℕ) : roundedSliceNode n m 0 = 0 := by
  norm_num [roundedSliceNode, idealSliceNode, chebyshevNode]

theorem roundedSliceNode_last {m : ℕ} (hm : 0 < m) (n : ℕ) : roundedSliceNode n m m = n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : chebyshevNode m m = -1 := by
    rw [chebyshevNode, mul_div_cancel_left₀ _ hm0, Real.cos_pi]
  rw [roundedSliceNode, idealSliceNode, hc]
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> nlinarith

/-- Lemma 2.2: nearest-integer Chebyshev slice nodes are strictly increasing when `n>m²`. -/
theorem roundedSliceNode_lt {n m j l : ℕ} (hm : 0 < m) (hn : m ^ 2 < n)
    (hjl : j < l) (hlm : l ≤ m) : roundedSliceNode n m j < roundedSliceNode n m l := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiff : (1 : ℝ) ≤ (l : ℝ) - j := by
    have hcast : (j : ℝ) + 1 ≤ l := by exact_mod_cast (show j + 1 ≤ l by omega)
    linarith
  have hsq : (1 : ℝ) ≤ ((l : ℝ) - j) ^ 2 := by nlinarith
  have hgap := chebyshevNode_gap hm hjl.le hlm
  have hgap0 : 2 / (m : ℝ) ^ 2 ≤ chebyshevNode m j - chebyshevNode m l := by
    have hmult := mul_le_mul_of_nonneg_left hsq
      (show (0 : ℝ) ≤ 2 / (m : ℝ) ^ 2 by positivity)
    have hmult' : 2 / (m : ℝ) ^ 2 ≤
        2 / (m : ℝ) ^ 2 * ((l : ℝ) - j) ^ 2 := by simpa using hmult
    exact hmult'.trans hgap
  have htarget : (n : ℝ) / (m : ℝ) ^ 2 ≤ idealSliceNode n m l - idealSliceNode n m j := by
    calc
      _ = (n : ℝ) / 2 * (2 / (m : ℝ) ^ 2) := by ring
      _ ≤ (n : ℝ) / 2 * (chebyshevNode m j - chebyshevNode m l) :=
        mul_le_mul_of_nonneg_left hgap0 (by positivity)
      _ = _ := by unfold idealSliceNode; ring
  have hnR : (m : ℝ) ^ 2 < n := by exact_mod_cast hn
  have hgt : (1 : ℝ) < (n : ℝ) / (m : ℝ) ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hmR)).mpr
    simpa using hnR
  have hj := roundedSliceNode_band n m j
  have hl := roundedSliceNode_band n m l
  have he : (roundedSliceNode n m j : ℝ) < roundedSliceNode n m l := by linarith
  exact_mod_cast he

theorem roundedSliceNode_strictMono {n m : ℕ} (hm : 0 < m) (hn : m ^ 2 < n) :
    StrictMono (fun j : Fin (m + 1) ↦ roundedSliceNode n m j.val) := by
  intro j l hjl
  exact roundedSliceNode_lt hm hn hjl (by have := l.isLt; omega)

end NoncommutativeAMGM
