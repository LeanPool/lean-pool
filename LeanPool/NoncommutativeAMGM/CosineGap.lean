/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Quantitative separation of the Chebyshev extrema -/

@[expose] public section
namespace NoncommutativeAMGM
open Real

theorem cosine_gap_lower {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ Real.pi) (hxy : x ≤ y) :
    (2 / Real.pi ^ 2) * (y - x) ^ 2 ≤ Real.cos x - Real.cos y := by
  let a := (x + y) / 2
  let b := (y - x) / 2
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbπ : b ≤ Real.pi / 2 := by dsimp [b]; linarith
  have hab : b ≤ a := by dsimp [a, b]; linarith
  have hba : b ≤ Real.pi - a := by dsimp [a, b]; linarith
  have hsinb : 0 ≤ Real.sin b :=
    Real.sin_nonneg_of_nonneg_of_le_pi hb0 (by linarith [Real.pi_pos])
  have hsina : Real.sin b ≤ Real.sin a := by
    by_cases ha : a ≤ Real.pi / 2
    · exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], hbπ⟩
        ⟨by linarith [Real.pi_pos], ha⟩ hab
    · rw [← Real.sin_pi_sub a]
      exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], hbπ⟩
        ⟨by linarith [Real.pi_pos], by linarith⟩ hba
  have hJordan := Real.mul_le_sin hb0 hbπ
  have hlin : 0 ≤ 2 / Real.pi * b := by positivity
  have hsq := mul_self_le_mul_self hlin hJordan
  have hprod := mul_le_mul_of_nonneg_right hsina hsinb
  have hdiff : Real.cos x - Real.cos y = 2 * Real.sin a * Real.sin b := by
    rw [Real.cos_sub_cos]
    change -2 * Real.sin a * Real.sin ((x - y) / 2) = _
    rw [show (x - y) / 2 = -b by dsimp [b]; ring, Real.sin_neg]
    ring
  have hnorm : (2 / Real.pi ^ 2) * (y - x) ^ 2 = 2 * (2 / Real.pi * b) ^ 2 := by
    dsimp [b]
    field_simp
  rw [hnorm, hdiff]
  nlinarith

/-- The `j`th Chebyshev extremum, with the paper's decreasing order. -/
noncomputable def chebyshevNode (m j : ℕ) : ℝ := Real.cos ((j : ℝ) * Real.pi / m)

/-- Distinct extrema are separated by at least `2/m²` times the squared index gap. -/
theorem chebyshevNode_gap {m j l : ℕ} (hm : 0 < m) (hjl : j ≤ l) (hlm : l ≤ m) :
    (2 / (m : ℝ) ^ 2) * ((l : ℝ) - j) ^ 2 ≤ chebyshevNode m j - chebyshevNode m l := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjlR : (j : ℝ) ≤ l := by exact_mod_cast hjl
  have hlmR : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have hx : 0 ≤ (j : ℝ) * Real.pi / m := by positivity
  have hy : (l : ℝ) * Real.pi / m ≤ Real.pi := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith [Real.pi_pos]
  have hxy : (j : ℝ) * Real.pi / m ≤ (l : ℝ) * Real.pi / m := by gcongr
  have he := cosine_gap_lower hx hy hxy
  change _ ≤ chebyshevNode m j - chebyshevNode m l at he
  convert he using 1
  field_simp

end NoncommutativeAMGM
