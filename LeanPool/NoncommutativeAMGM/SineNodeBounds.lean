/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RoundedNodes

/-! # The interior Chebyshev slice interval in Theorem 3.5 -/

@[expose] public section
namespace NoncommutativeAMGM

@[simp] theorem idealSliceNode_zero (n m : ℕ) : idealSliceNode n m 0 = 0 := by
  simp [idealSliceNode, chebyshevNode]

theorem idealSliceNode_last {m : ℕ} (hm : 0 < m) (n : ℕ) : idealSliceNode n m m = n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold idealSliceNode chebyshevNode
  rw [mul_div_cancel_left₀ _ hm0, Real.cos_pi]
  ring

theorem idealSliceNode_mono {m j l : ℕ} (hm : 0 < m) (hjl : j ≤ l) (hlm : l ≤ m) (n : ℕ) :
    idealSliceNode n m j ≤ idealSliceNode n m l := by
  have hgap := chebyshevNode_gap hm hjl hlm
  have hnonneg : (0 : ℝ) ≤ 2 / (m : ℝ) ^ 2 * ((l : ℝ) - j) ^ 2 := by positivity
  have hcos : chebyshevNode m l ≤ chebyshevNode m j := by linarith
  unfold idealSliceNode
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem chebyshevNode_complement {m j : ℕ} (hm : 0 < m) (hjm : j ≤ m) :
    chebyshevNode m (m - j) = -chebyshevNode m j := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold chebyshevNode
  have he : ((m - j : ℕ) : ℝ) * Real.pi / m = Real.pi - (j : ℝ) * Real.pi / m := by
    rw [Nat.cast_sub hjm]
    field_simp
  rw [he, Real.cos_pi_sub]

theorem idealSliceNode_complement {m j : ℕ} (hm : 0 < m) (hjm : j ≤ m) (n : ℕ) :
    idealSliceNode n m (m - j) = (n : ℝ) - idealSliceNode n m j := by
  unfold idealSliceNode
  rw [chebyshevNode_complement hm hjm]
  ring

theorem idealSliceNode_first {m : ℕ} (hm : 0 < m) (n : ℕ) :
    idealSliceNode n m 1 = (n : ℝ) * Real.sin (Real.pi / (2 * (m : ℝ))) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : 2 * (Real.pi / (2 * (m : ℝ))) = Real.pi / m := by field_simp
  rw [Real.sin_sq_eq_half_sub, he]
  unfold idealSliceNode chebyshevNode
  norm_num
  ring

/-- The sine-node hypothesis places every interior slice in the positivity interval. -/
theorem idealSliceNode_interior {m j d n : ℕ} (hm : 0 < m) (hj : 0 < j) (hjm : j < m)
    (hsin : (d : ℝ) - 1 ≤ (n : ℝ) * Real.sin (Real.pi / (2 * (m : ℝ))) ^ 2) :
    (d : ℝ) - 1 ≤ idealSliceNode n m j ∧
      (d : ℝ) - 1 ≤ (n : ℝ) - idealSliceNode n m j := by
  have hfirst : (d : ℝ) - 1 ≤ idealSliceNode n m 1 := by
    rwa [idealSliceNode_first hm n]
  constructor
  · exact hfirst.trans (idealSliceNode_mono hm (by omega) hjm.le n)
  · have hother := idealSliceNode_mono (j := 1) (l := m - j) hm (by omega) (by omega) n
    rw [idealSliceNode_complement hm hjm.le n] at hother
    exact hfirst.trans hother

end NoncommutativeAMGM
