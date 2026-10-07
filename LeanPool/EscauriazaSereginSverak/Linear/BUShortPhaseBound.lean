/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSubquadratic
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhase

/-!
# Quadratic control of the normal phase

On the short normalized time interval, the normal Carleman phase has
at most three-halves growth in height and is absorbed by a Gaussian.
-/

public section


open Set

noncomputable section

namespace ESS

/-- The normal phase is at most the three-halves power of height for
normalized times between one half and one (`lem:bu-small-time`). -/
theorem bu_short_F_le_three_halves
    (y s : ℝ) (hy : 0 ≤ y) (hs : s ∈ Ioo (1 / 2 : ℝ) 1) :
    buShortF y s ≤ y ^ (3 / 2 : ℝ) := by
  have hmono := buShortF_antitone_time hy
    (by norm_num : (0 : ℝ) < 1 / 2) hs.1.le hs.2.le
  have hpow : (1 / 2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤
      (1 / 2 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (by norm_num : (-(1 : ℝ)) ≤ -(3 / 4 : ℝ))
  have htwo : (1 / 2 : ℝ) ^ (-(1 : ℝ)) = 2 := by norm_num
  rw [htwo] at hpow
  have hyPow : 0 ≤ y ^ (3 / 2 : ℝ) := by positivity
  have hhalf : buShortF y (1 / 2) ≤ y ^ (3 / 2 : ℝ) := by
    dsimp [buShortF]
    nlinarith only [mul_le_mul_of_nonneg_left hpow hyPow]
  exact hmono.trans hhalf

/-- A fixed normal phase factor is bounded by an arbitrarily small
quadratic term plus a constant. -/
theorem bu_short_F_subquadratic_bound
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y s : ℝ, 0 ≤ y → s ∈ Ioo (1 / 2 : ℝ) 1 →
        2 * a * buShortF y s ≤ b * y ^ 2 / 2 + C := by
  obtain ⟨C, hC, hbound⟩ :=
    bu_short_subquadratic_bound (2 * a) b (by positivity) hb
  refine ⟨C, hC, ?_⟩
  intro y s hy hs
  have hF := bu_short_F_le_three_halves y s hy hs
  have hmul := mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ 2 * a)
  exact hmul.trans (hbound y hy)

end ESS
