/-
Copyright (c) 2026 Xuanji Li and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li, Lean Pool contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real interval certificates for the Chudnovsky coefficients

Prove the numeric enclosures independently of the modular-form and lattice developments.
Rounded coefficient and factor intervals keep the arithmetic certificates small.
-/

public section

namespace Chudnovsky.NumericalBounds

/-- Enclose the real approximation to the singular j-value within half a unit. -/
theorem jwert_real_bound {e : ℝ}
    (hL : (3.80898093700765233822623151647e-18 : ℝ) < e)
    (hU : e < (3.80898093700765233822623151648e-18 : ℝ)) :
    |(1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) - 640320 ^ 3| < 1 / 2 := by
  -- The final tolerance is one half, so coarse rational enclosures suffice.
  have hL : (3.808980937007652338e-18 : ℝ) < e := lt_trans (by norm_num1) hL
  have hU : e < (3.808980937007652339e-18 : ℝ) := lt_trans hU (by norm_num1)
  have hepos : 0 < e := lt_trans (by norm_num1) hL
  have he2U : e ^ 2 ≤ (3.808980937007652339e-18 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hepos.le hU.le 2
  have he2nn : 0 ≤ e ^ 2 := sq_nonneg e
  -- enclosures for `g = 1 - 240e + 2160e²`
  have hGLg : (1 - 240 * 3.808980937007652339e-18 : ℝ)
      ≤ 1 - 240 * e + 2160 * e ^ 2 := by linarith only [hU, he2nn]
  have hgGH : 1 - 240 * e + 2160 * e ^ 2 ≤
      (1 - 240 * 3.808980937007652338e-18
        + 2160 * (3.808980937007652339e-18) ^ 2 : ℝ) := by linarith only [hL, he2U]
  have hGLpos : (0 : ℝ) < 1 - 240 * 3.808980937007652339e-18 := by norm_num1
  have hgpos : 0 < 1 - 240 * e + 2160 * e ^ 2 := lt_of_lt_of_le hGLpos hGLg
  -- enclosures for `h = 1 + e - e²`
  have hHLh : (1 + 3.808980937007652338e-18
      - (3.808980937007652339e-18) ^ 2 : ℝ) ≤ 1 + e - e ^ 2 := by
    linarith only [hL, he2U]
  have hhHH : 1 + e - e ^ 2 ≤ (1 + 3.808980937007652339e-18 : ℝ) := by
    linarith only [hU, he2nn]
  have hHLpos : (0 : ℝ) < 1 + 3.808980937007652338e-18
      - (3.808980937007652339e-18) ^ 2 := by norm_num1
  have hhpos : 0 < 1 + e - e ^ 2 := lt_of_lt_of_le hHLpos hHLh
  -- cube / 24-th power the enclosures
  have hN_hi : (1 - 240 * e + 2160 * e ^ 2) ^ 3 ≤
      (1 - 240 * 3.808980937007652338e-18
        + 2160 * (3.808980937007652339e-18) ^ 2) ^ 3 :=
    pow_le_pow_left₀ hgpos.le hgGH 3
  have hN_lo : (1 - 240 * 3.808980937007652339e-18) ^ 3
      ≤ (1 - 240 * e + 2160 * e ^ 2) ^ 3 := pow_le_pow_left₀ hGLpos.le hGLg 3
  have hW_hi : (1 + e - e ^ 2) ^ 24 ≤ (1 + 3.808980937007652339e-18) ^ 24 :=
    pow_le_pow_left₀ hhpos.le hhHH 24
  have hW_lo : (1 + 3.808980937007652338e-18
      - (3.808980937007652339e-18) ^ 2) ^ 24 ≤ (1 + e - e ^ 2) ^ 24 :=
    pow_le_pow_left₀ hHLpos.le hHLh 24
  -- the two division enclosures of `S`
  have hden_pos : 0 < e * (1 + e - e ^ 2) ^ 24 := mul_pos hepos (pow_pos hhpos 24)
  have hSupper : (1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) ≤
      (1 - 240 * 3.808980937007652338e-18
        + 2160 * (3.808980937007652339e-18) ^ 2) ^ 3 /
        (3.808980937007652338e-18 *
          (1 + 3.808980937007652338e-18
            - (3.808980937007652339e-18) ^ 2) ^ 24) := by
    apply div_le_div₀ (by positivity) hN_hi
      (mul_pos (by norm_num1) (pow_pos hHLpos 24))
    exact mul_le_mul hL.le hW_lo (pow_nonneg hHLpos.le 24) hepos.le
  have hSlower : (1 - 240 * 3.808980937007652339e-18) ^ 3 /
        (3.808980937007652339e-18 *
          (1 + 3.808980937007652339e-18) ^ 24) ≤
      (1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) := by
    apply div_le_div₀ (by positivity) hN_lo hden_pos
    exact mul_le_mul hU.le hW_hi (pow_nonneg hhpos.le 24) (by norm_num1)
  -- the two heavy rational inequalities
  have hUpNum : (1 - 240 * 3.808980937007652338e-18
        + 2160 * (3.808980937007652339e-18) ^ 2) ^ 3 /
        (3.808980937007652338e-18 *
          (1 + 3.808980937007652338e-18
            - (3.808980937007652339e-18) ^ 2) ^ 24) < (640320 : ℝ) ^ 3 + 1 / 2 := by
    norm_num1
  have hLoNum : (640320 : ℝ) ^ 3 - 1 / 2 <
      (1 - 240 * 3.808980937007652339e-18) ^ 3 /
        (3.808980937007652339e-18 *
          (1 + 3.808980937007652339e-18) ^ 24) := by
    norm_num1
  rw [abs_lt]
  exact ⟨by linarith only [hLoNum.trans_le hSlower],
    by linarith only [hSupper.trans_lt hUpNum]⟩

/-- Enclose the scaled real approximation to `s₂` within half a unit. -/
theorem s2tilde_real_bound {e pv sv : ℝ}
    (heL : (3.80898093700765233822623151647e-18 : ℝ) < e)
    (heU : e < (3.80898093700765233822623151648e-18 : ℝ))
    (hpL : (3.14159265358979323846 : ℝ) < pv) (hpU : pv < (3.14159265358979323847 : ℝ))
    (hsL : (12.7671453348037046617 : ℝ) < sv) (hsU : sv < (12.7671453348037046618 : ℝ)) :
    |(1 - 240 * e + 2160 * e ^ 2) / (1 + 504 * e - 16632 * e ^ 2)
        * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2))) * 10996566783048
        - 9351571368960| < 1 / 2 := by
  have heL : (3e-18 : ℝ) < e := lt_trans (by norm_num1) heL
  have heU : e < (4e-18 : ℝ) := lt_trans heU (by norm_num1)
  have hpL : (3.14159265358979 : ℝ) < pv := lt_trans (by norm_num1) hpL
  have hpU : pv < (3.14159265358980 : ℝ) := lt_trans hpU (by norm_num1)
  have hsL : (12.7671453348037 : ℝ) < sv := lt_trans (by norm_num1) hsL
  have hsU : sv < (12.7671453348038 : ℝ) := lt_trans hsU (by norm_num1)
  have hepos : 0 < e := lt_trans (by norm_num1) heL
  have hp_pos : 0 < pv := lt_trans (by norm_num1) hpL
  have hs_pos : 0 < sv := lt_trans (by norm_num1) hsL
  have he2U : e ^ 2 ≤ (4e-18 : ℝ) ^ 2 := pow_le_pow_left₀ hepos.le heU.le 2
  have he2nn : 0 ≤ e ^ 2 := sq_nonneg e
  have hdenpos : 0 < 1 + 504 * e - 16632 * e ^ 2 := by linarith only [heL, he2U]
  let R := (1 - 240 * e + 2160 * e ^ 2) / (1 + 504 * e - 16632 * e ^ 2)
  let Z := 1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2))
  change |R * Z * 10996566783048 - 9351571368960| < 1 / 2
  -- Round the first factor near one before combining the interval estimates.
  have hRL : (1 - 1e-14 : ℝ) ≤ R := by
    apply (le_div_iff₀ hdenpos).mpr
    linarith only [heU, he2nn]
  have hRH : R ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hdenpos).mpr
    linarith only [heL, he2U]
  have hdivision : 3 / (pv * (sv / 2)) = 6 / (pv * sv) := by ring
  have hwH : 6 / (pv * sv) ≤ (6 / (3.14159265358979 * 12.7671453348037) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num1) (by norm_num1)
      (mul_le_mul hpL.le hsL.le (by norm_num1) hp_pos.le)
  have hwL : (6 / (3.14159265358980 * 12.7671453348038) : ℝ) ≤ 6 / (pv * sv) :=
    div_le_div_of_nonneg_left (by norm_num1) (mul_pos hp_pos hs_pos)
      (mul_le_mul hpU.le hsU.le hs_pos.le (by norm_num1))
  -- Enclose the second factor directly around the final rational value.
  have hZL : (9351571368960 / 10996566783048 - 1e-14 : ℝ) ≤ Z := by
    have hnumeric : (9351571368960 / 10996566783048 - 1e-14 : ℝ)
        ≤ 1 + 24 * 3e-18 - 72 * (4e-18) ^ 2
          - 6 / (3.14159265358979 * 12.7671453348037) := by norm_num1
    dsimp [Z]
    rw [hdivision]
    linarith only [hnumeric, heL, he2U, hwH]
  have hZH : Z ≤ (9351571368960 / 10996566783048 + 1e-14 : ℝ) := by
    have hnumeric : (1 + 24 * 4e-18
        - 6 / (3.14159265358980 * 12.7671453348038) : ℝ)
        ≤ 9351571368960 / 10996566783048 + 1e-14 := by norm_num1
    dsimp [Z]
    rw [hdivision]
    linarith only [hnumeric, heU, he2nn, hwL]
  have hRnonneg : 0 ≤ R := le_trans (by norm_num1) hRL
  have hZnonneg : 0 ≤ Z := le_trans (by norm_num1) hZL
  have hlo := mul_le_mul_of_nonneg_right
    (mul_le_mul hRL hZL (by norm_num1) hRnonneg)
    (by norm_num1 : (0 : ℝ) ≤ 10996566783048)
  have hhi := mul_le_mul_of_nonneg_right
    (mul_le_mul hRH hZH hZnonneg (by norm_num1))
    (by norm_num1 : (0 : ℝ) ≤ 10996566783048)
  have hlow : (9351571368960 : ℝ) - 1 / 2
      < (1 - 1e-14) * (9351571368960 / 10996566783048 - 1e-14) * 10996566783048 := by
    norm_num1
  have hhigh : (1 : ℝ) * (9351571368960 / 10996566783048 + 1e-14) * 10996566783048
      < 9351571368960 + 1 / 2 := by norm_num1
  rw [abs_lt]
  exact ⟨by linarith only [hlo, hlow], by linarith only [hhi, hhigh]⟩


end Chudnovsky.NumericalBounds
