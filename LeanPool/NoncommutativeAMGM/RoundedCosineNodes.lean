/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RoundedNodes

/-! # Rounded Chebyshev nodes in cosine coordinates -/

@[expose] public section

namespace NoncommutativeAMGM

/-- The shifted cosine node `tⱼ = 1 - 2sⱼ/n` of Section 2.3. -/
noncomputable def roundedCosineNode (n m j : ℕ) : ℝ :=
  1 - 2 * (roundedSliceNode n m j : ℝ) / (n : ℝ)

theorem roundedCosineNode_mem {n : ℕ} (hn : 0 < n) (m j : ℕ) :
    roundedCosineNode n m j ∈ Set.Icc (-1) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (roundedSliceNode n m j : ℝ) ≤ n := by exact_mod_cast roundedSliceNode_le n m j
  have hs0 : (0 : ℝ) ≤ roundedSliceNode n m j := by positivity
  dsimp [roundedCosineNode]
  constructor
  · have : 2 * (roundedSliceNode n m j : ℝ) / (n : ℝ) ≤ 2 :=
      (div_le_iff₀ hn').mpr (by linarith)
    linarith
  · have : 0 ≤ 2 * (roundedSliceNode n m j : ℝ) / (n : ℝ) := by positivity
    linarith

theorem roundedCosineNode_error {n : ℕ} (hn : 0 < n) (m j : ℕ) :
    |roundedCosineNode n m j - chebyshevNode m j| ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := roundedSliceNode_error n m j
  have he : roundedCosineNode n m j - chebyshevNode m j =
      -(2 / (n : ℝ)) * ((roundedSliceNode n m j : ℝ) - idealSliceNode n m j) := by
    dsimp [roundedCosineNode, idealSliceNode]
    field_simp
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 / (n : ℝ))]
  calc
    _ ≤ (2 / (n : ℝ)) * (1 / 2) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

@[simp] theorem roundedCosineNode_zero (n m : ℕ) : roundedCosineNode n m 0 = 1 := by
  simp [roundedCosineNode]

theorem roundedCosineNode_last {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    roundedCosineNode n m m = -1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  norm_num [roundedCosineNode, roundedSliceNode_last hm, hn0]

theorem roundedCosineNode_strictAnti {n m : ℕ} (hm : 0 < m) (hn : m ^ 2 < n) :
    StrictAnti (fun j : Fin (m + 1) ↦ roundedCosineNode n m j.val) := by
  intro j l hjl
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (roundedSliceNode n m j : ℝ) < roundedSliceNode n m l := by
    exact_mod_cast (roundedSliceNode_strictMono hm hn hjl)
  dsimp [roundedCosineNode]
  have h : 2 * (roundedSliceNode n m j : ℝ) / (n : ℝ) <
      2 * (roundedSliceNode n m l : ℝ) / (n : ℝ) :=
    (div_lt_div_iff_of_pos_right hn').mpr (by linarith)
  linarith

theorem roundedCosineNode_injOn {n m : ℕ} (hm : 0 < m) (hn : m ^ 2 < n) :
    Set.InjOn (roundedCosineNode n m) (Finset.range (m + 1)) := by
  intro j hj l hl he
  have h := (roundedCosineNode_strictAnti hm hn).injective
    (a₁ := ⟨j, Finset.mem_range.mp hj⟩) (a₂ := ⟨l, Finset.mem_range.mp hl⟩) he
  exact congrArg Fin.val h

end NoncommutativeAMGM
