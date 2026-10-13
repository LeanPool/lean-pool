/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalRegime
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootPayloadPrefix

/-!
# RootClauseBFinalFunding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `C₁`-floor form of the Step-6 gate -/

/-- **The Step-6 funding floor** `(2·P·C_ann·(s/8)·3^{k/4})²`. -/
def rootClauseBFundFloor (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) : ℝ :=
  (2 * (edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth) *
    stepOneThreePow k) ^ (2 : ℕ)

/-- **The Step-6 funding line from a pure `C₁`-floor.**

No division, and no positivity of `edFinalEpsCoeff` is needed: the whole
argument is `√δ ≤ (√C₁)⁻¹` followed by one cross-multiplication. -/
theorem edFunding_of_c1_floor (d : ℕ) [NeZero d] {C Cann C1 alpha : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hCann : 0 ≤ Cann) (halpha0 : 0 ≤ alpha)
    (hC1 : 0 < C1) (hfloor : rootClauseBFundFloor d C Cann k ≤ C1) :
    edFinalEpsCoeff d C k stepOneS * (Cann * stepOneEp (stepOneDelta C1 alpha)) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) := by
  have hP : (0 : ℝ) ≤ edFinalEpsCoeff d C k stepOneS :=
    edFinalEpsCoeff_nonneg d hC k (by rw [stepOneS]; norm_num)
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  set T : ℝ := stepOneThreePow k with hTdef
  set Q : ℝ := edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth with hQdef
  have hQ : (0 : ℝ) ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg hP hCann) stepOneSEighth_pos.le
  have hfl2 : (2 * Q * T) ^ (2 : ℕ) ≤ C1 := by
    rw [hQdef, hTdef]
    exact hfloor
  have hTne : T ≠ 0 := ne_of_gt hT
  have hsc : (0 : ℝ) < Real.sqrt C1 := Real.sqrt_pos.mpr hC1
  have hscne : Real.sqrt C1 ≠ 0 := ne_of_gt hsc
  -- `√δ ≤ (√C₁)⁻¹`
  have hdle : stepOneDelta C1 alpha ≤ C1⁻¹ := by
    rw [stepOneDelta]
    have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha0]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hC1).le
    rw [mul_one] at h2
    exact h2
  have hsq : Real.sqrt (stepOneDelta C1 alpha) ≤ (Real.sqrt C1)⁻¹ := by
    have h := Real.sqrt_le_sqrt hdle
    rwa [Real.sqrt_inv] at h
  -- `2QT ≤ √C₁`
  have hfl : 2 * Q * T ≤ Real.sqrt C1 := by
    have h0 : (0 : ℝ) ≤ 2 * Q * T := mul_nonneg (by linarith only [hQ]) hT.le
    have h := Real.sqrt_le_sqrt hfl2
    rwa [Real.sqrt_sq h0] at h
  -- the cross-multiplication
  have hmul : (0 : ℝ) ≤ (Real.sqrt C1)⁻¹ * (2 * T)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hsc.le) (inv_nonneg.mpr (by linarith only [hT]))
  have hcross := mul_le_mul_of_nonneg_right hfl hmul
  have e1 : 2 * Q * T * ((Real.sqrt C1)⁻¹ * (2 * T)⁻¹) = Q * (Real.sqrt C1)⁻¹ := by
    field_simp
  have e2 : Real.sqrt C1 * ((Real.sqrt C1)⁻¹ * (2 * T)⁻¹) = 1 / 2 * T⁻¹ := by
    field_simp
  rw [e1, e2] at hcross
  have hLHS : edFinalEpsCoeff d C k stepOneS *
      (Cann * stepOneEp (stepOneDelta C1 alpha)) =
      Q * Real.sqrt (stepOneDelta C1 alpha) := by
    rw [hQdef, stepOneEp]
    ring
  have hexp : (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) = T⁻¹ := by
    have he : -(1 / 4 : ℝ) * (k : ℝ) = -(k : ℝ) / 4 := by ring
    rw [he, hTdef]
    exact rpow_three_neg_quarter k
  rw [hLHS, hexp]
  calc Q * Real.sqrt (stepOneDelta C1 alpha)
      ≤ Q * (Real.sqrt C1)⁻¹ := mul_le_mul_of_nonneg_left hsq hQ
    _ ≤ 1 / 2 * T⁻¹ := hcross

/-! ## 2. The Step-1 `δ`-slot, evaluated -/

/-- **The Step-1 `C₁` slot, in closed form**: `stepOne C_edos C_ann k = (2 C_edos
C_ann 3^{k/4})²/s`. -/
theorem stepOneC1Delta0_eq {Cedos Cann : ℝ} (hCedos : 0 < Cedos) (hCann : 0 < Cann)
    (k : ℕ) :
    stepOneC1Delta0 Cedos Cann k =
      (2 * Cedos * Cann * stepOneThreePow k) ^ (2 : ℕ) / stepOneS := by
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hs : Real.sqrt stepOneS ^ (2 : ℕ) = stepOneS :=
    Real.sq_sqrt (by rw [stepOneS]; norm_num)
  have hX : (2 * Cedos * Cann * stepOneThreePow k) ≠ 0 := by
    have : (0 : ℝ) < 2 * Cedos * Cann * stepOneThreePow k :=
      mul_pos (mul_pos (mul_pos (by norm_num) hCedos) hCann) hT
    exact ne_of_gt this
  have hbase : stepOneDelta0 Cedos Cann k =
      stepOneS / (2 * Cedos * Cann * stepOneThreePow k) ^ (2 : ℕ) := by
    rw [stepOneDelta0, mul_pow, hs, inv_pow]
    field_simp
  rw [stepOneC1Delta0, hbase, inv_div]

/-! ## 3. The floor, discharged at explicit constants -/

/-- **The Step-1 excess-decay letter that funds the Step-6 gate**: `C_edos = max 1
(P·C_ann·(s/8))`.  It meets the printed floor `1 ≤ C_edos`  by construction. -/
def rootClauseBFundCedos (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) : ℝ :=
  max 1 (edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth)

theorem one_le_rootClauseBFundCedos (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) :
    1 ≤ rootClauseBFundCedos d C Cann k := le_max_left _ _

theorem rootClauseBFundCedos_pos (d : ℕ) [NeZero d] (C Cann : ℝ) (k : ℕ) :
    0 < rootClauseBFundCedos d C Cann k :=
  lt_of_lt_of_le (by norm_num) (one_le_rootClauseBFundCedos d C Cann k)

/-- **The floor is met by the root's own `C₁`.**

`stepOneC1` dominates its `δ`-slot, which at `C_ann' = 1` and the explicit
`C_edos` above equals `4·(2 C_edos 3^{k/4})²` (because `s = 1/4`), and that
dominates `(2·P·C_ann·(s/8)·3^{k/4})²`. -/
theorem rootClauseBFundFloor_le_stepOneC1 (d : ℕ) [NeZero d] {C Cann : ℝ} (hC : 0 ≤ C)
    (hCann : 0 ≤ Cann) (Citer : ℝ) (k : ℕ) :
    rootClauseBFundFloor d C Cann k ≤
      stepOneC1 d (rootClauseBFundCedos d C Cann k) 1 Citer k := by
  have hP : (0 : ℝ) ≤ edFinalEpsCoeff d C k stepOneS :=
    edFinalEpsCoeff_nonneg d hC k (by rw [stepOneS]; norm_num)
  have hT : (0 : ℝ) < stepOneThreePow k := stepOneThreePow_pos k
  have hQ : (0 : ℝ) ≤ edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth :=
    mul_nonneg (mul_nonneg hP hCann) stepOneSEighth_pos.le
  have hCe := rootClauseBFundCedos_pos d C Cann k
  have hle : edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth ≤
      rootClauseBFundCedos d C Cann k := le_max_right _ _
  have hstep : rootClauseBFundFloor d C Cann k ≤
      (2 * rootClauseBFundCedos d C Cann k * 1 * stepOneThreePow k) ^ (2 : ℕ) := by
    rw [rootClauseBFundFloor]
    refine pow_le_pow_left₀ ?_ ?_ 2
    · exact mul_nonneg (by linarith only [hQ]) hT.le
    · have h1 : 2 * (edFinalEpsCoeff d C k stepOneS * Cann * stepOneSEighth) ≤
          2 * rootClauseBFundCedos d C Cann k * 1 := by linarith only [hle]
      exact mul_le_mul_of_nonneg_right h1 hT.le
  have hslot : (2 * rootClauseBFundCedos d C Cann k * 1 * stepOneThreePow k) ^ (2 : ℕ) ≤
      stepOneC1Delta0 (rootClauseBFundCedos d C Cann k) 1 k := by
    rw [stepOneC1Delta0_eq hCe one_pos k, stepOneS]
    have hsq : (0 : ℝ) ≤
        (2 * rootClauseBFundCedos d C Cann k * 1 * stepOneThreePow k) ^ (2 : ℕ) :=
      sq_nonneg _
    rw [div_eq_mul_inv]
    norm_num
    linarith only [hsq]
  have hmax : stepOneC1Delta0 (rootClauseBFundCedos d C Cann k) 1 k ≤
      stepOneC1 d (rootClauseBFundCedos d C Cann k) 1 Citer k :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact le_trans hstep (le_trans hslot hmax)

end

end Algsuperdiff.Section4.Provider.Regularity
