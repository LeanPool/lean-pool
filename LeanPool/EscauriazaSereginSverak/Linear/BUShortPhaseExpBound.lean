/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseDecay

/-!
# Exponential normal-phase bound

At fixed Carleman parameter, the normal phase exponential is bounded by
an arbitrarily weak quadratic exponential times a constant.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A fixed shifted normal phase is dominated by a quadratic Gaussian
exponent on the short-time slab (`lem:bu-small-time`). -/
theorem bu_short_normal_phase_exp_le_quadratic
    (scale a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ParabolicPoint, 0 ≤ z.1 2 →
        z.2 ∈ Ioo (1 / 2 : ℝ) 1 →
        Real.exp (2 * a * (buShortF (z.1 2) z.2 - buShortB scale)) ≤
          C * Real.exp (b * z.1 2 ^ 2) := by
  obtain ⟨C₀, hC₀, hphase⟩ :=
    bu_short_F_subquadratic_bound a (2 * b) ha (by positivity)
  let C := Real.exp (C₀ + 2 * a * |buShortB scale|)
  have hC : 0 < C := Real.exp_pos _
  refine ⟨C, hC, ?_⟩
  intro z hy hs
  have hF := hphase (z.1 2) z.2 hy hs
  have hB : -buShortB scale ≤ |buShortB scale| := neg_le_abs _
  have hBmul := mul_le_mul_of_nonneg_left hB
    (by positivity : 0 ≤ 2 * a)
  have harg : 2 * a * (buShortF (z.1 2) z.2 - buShortB scale) ≤
      C₀ + 2 * a * |buShortB scale| + b * z.1 2 ^ 2 := by
    nlinarith only [hF, hBmul]
  have hExp := Real.exp_le_exp.mpr harg
  rw [Real.exp_add] at hExp
  simpa only [C] using hExp

end ESS
