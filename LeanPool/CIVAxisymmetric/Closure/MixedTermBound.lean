/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
This is the final Young's-inequality absorption of the mixed-term bound
`eq:aniso:closure:mixed:bound` of `lem:aniso:closure`,
arXiv:2609.20803, with the Cauchy–Schwarz/elliptic inputs abstracted as the
real hypothesis `hI`.
-/

public section

noncomputable section
namespace CIV


theorem mixed_term_bound_of_cauchy_schwarz {I C C₁ W M Y : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hI : |I| ≤ C + C₁ * W * Real.sqrt (M + 1) * Real.sqrt Y
        + C₁ * W * Real.sqrt (Y + 1) * Real.sqrt M) :
    |I| ≤ (1 / 4) * M + (C + 1 / 8 + 4 * C₁ ^ 2) * (W ^ 2 + 1) * (Y + 1) := by
  set a1 := Real.sqrt (M + 1) with ha1_def
  set b1 := Real.sqrt Y with hb1_def
  set a2 := Real.sqrt M with ha2_def
  set b2 := Real.sqrt (Y + 1) with hb2_def
  have ha1sq : a1 ^ 2 = M + 1 := Real.sq_sqrt (by linarith only [hM])
  have hb1sq : b1 ^ 2 = Y := Real.sq_sqrt hY
  have ha2sq : a2 ^ 2 = M := Real.sq_sqrt hM
  have hb2sq : b2 ^ 2 = Y + 1 := Real.sq_sqrt (by linarith only [hY])
  have hstep2 : C₁ * W * a1 * b1 ≤ (M + 1) / 8 + 2 * C₁ ^ 2 * W ^ 2 * Y := by
    have hsq : (a1 - 4 * C₁ * W * b1) ^ 2 ≥ 0 := sq_nonneg _
    have h_expanded : a1 ^ 2 - 8 * C₁ * W * a1 * b1 + 16 * C₁ ^ 2 * W ^ 2 * b1 ^ 2 ≥ 0 := by
      nlinarith only [hsq]
    rw [ha1sq, hb1sq] at h_expanded
    linarith only [h_expanded]
  have hstep3 : C₁ * W * b2 * a2 ≤ M / 8 + 2 * C₁ ^ 2 * W ^ 2 * (Y + 1) := by
    have hsq : (a2 - 4 * C₁ * W * b2) ^ 2 ≥ 0 := sq_nonneg _
    have h_expanded : a2 ^ 2 - 8 * C₁ * W * a2 * b2 + 16 * C₁ ^ 2 * W ^ 2 * b2 ^ 2 ≥ 0 := by
      nlinarith only [hsq]
    rw [ha2sq, hb2sq] at h_expanded
    linarith only [h_expanded]
  have h_mid : C + C₁ * W * a1 * b1 + C₁ * W * b2 * a2 ≤
      C + ((M + 1) / 8 + 2 * C₁ ^ 2 * W ^ 2 * Y) + (M / 8 + 2 * C₁ ^ 2 * W ^ 2 * (Y + 1)) := by
    linarith only [hstep2, hstep3]
  have hWsq_nonneg : 0 ≤ W ^ 2 := sq_nonneg W
  have hC1sq_nonneg : 0 ≤ C₁ ^ 2 := sq_nonneg C₁
  have h_denom_ge_one : 1 ≤ (W ^ 2 + 1) * (Y + 1) := by
    nlinarith only [hWsq_nonneg, hY]
  have hCpart : C ≤ C * ((W ^ 2 + 1) * (Y + 1)) := by
    nlinarith only [hC, h_denom_ge_one]
  have h18part : (1 : ℝ) / 8 ≤ (1 / 8) * ((W ^ 2 + 1) * (Y + 1)) := by
    nlinarith only [h_denom_ge_one]
  have hC1part : 4 * C₁ ^ 2 * W ^ 2 * Y + 2 * C₁ ^ 2 * W ^ 2 ≤
      4 * C₁ ^ 2 * ((W ^ 2 + 1) * (Y + 1)) := by
    nlinarith only [hC1sq_nonneg, mul_nonneg hC1sq_nonneg hY, mul_nonneg hC1sq_nonneg hWsq_nonneg]
  have h_final : C + ((M + 1) / 8 + 2 * C₁ ^ 2 * W ^ 2 * Y) + (M / 8 + 2 * C₁ ^ 2 * W ^ 2 * (Y +
    1)) ≤
      (1 / 4) * M + (C + 1 / 8 + 4 * C₁ ^ 2) * (W ^ 2 + 1) * (Y + 1) := by
    nlinarith only [hCpart, h18part, hC1part]
  exact le_trans hI (le_trans h_mid h_final)

end CIV
