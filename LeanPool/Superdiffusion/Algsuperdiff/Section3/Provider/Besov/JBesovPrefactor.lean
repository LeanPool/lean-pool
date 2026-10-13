/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# JBesovPrefactor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A uniform scalar envelope for the diagonal coarse Caccioppoli prefactor

The upstream coarse-grained Caccioppoli estimate keeps its exact parameter
factors: at parameters `s, t` its prefactor is

`(C/(1-s-t))^{2+4s/(1-s-t)} * s^{-2s/(1-s-t)} * \Theta_{s,t}^{s/(1-s-t)}
  * \Lambda_s * 3^{-2m}`.

In the range used by Section 3.5 of ABK26, namely the diagonal `t = s` with
`0 < s \le 1/4`, the first two factors depend only on `s` and on the
dimension-only Caccioppoli constant `C`, and they are uniformly bounded there.
This module proves that uniform bound, so that those two factors may be
absorbed into the dimension-only constant of the manuscript display while the
three displayed factors `\Theta^{s/(1-2s)}`, `\Lambda_s` and `3^{-2m}` are
retained verbatim.

The file is deliberately scalar-only: it neither applies nor restates the
Caccioppoli estimate, and it packages none of the response or duality terms.
The whole content is the scalar inequality
`caccioppoliScalarFactors_diag_le_jBesovEnvelope`, stated over abstract reals;
the second theorem is only its transcription onto the upstream prefactor.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open HCPolySupport HCPolySupport.Book

noncomputable section

/-- An explicit envelope for the two `s`-dependent scalar factors of the
diagonal coarse Caccioppoli prefactor.  It depends only on the upstream
dimension-only Caccioppoli constant. -/
noncomputable def jBesovCaccioppoliEnvelope (C : ℝ) : ℝ :=
  Real.exp 4 * Real.rpow (max 1 (2 * C)) 4

theorem jBesovCaccioppoliEnvelope_pos (C : ℝ) : 0 < jBesovCaccioppoliEnvelope C :=
  mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)

/-- **The scalar core.**  On the manuscript range `0 < s \le 1/4`, the product
of the two `s`-dependent factors of the diagonal Caccioppoli prefactor is
bounded by an envelope depending only on `C`.  The statement involves no cube,
no coefficient field and no dimension. -/
theorem caccioppoliScalarFactors_diag_le_jBesovEnvelope {C s : ℝ} (hC : 0 ≤ C)
    (hs : 0 < s) (hs_quarter : s ≤ 1 / 4) :
    Real.rpow (C / (1 - 2 * s)) (2 + 4 * s / (1 - 2 * s)) *
        Real.rpow s (-(2 * s / (1 - 2 * s))) ≤
      jBesovCaccioppoliEnvelope C := by
  have hdelta_half : (1 / 2 : ℝ) ≤ 1 - 2 * s := by linarith
  have hdelta_pos : (0 : ℝ) < 1 - 2 * s := by linarith
  have hbase_one : (1 : ℝ) ≤ max 1 (2 * C) := le_max_left _ _
  have hbase_nonneg : (0 : ℝ) ≤ max 1 (2 * C) := zero_le_one.trans hbase_one
  -- The exponent `2 + 4s/(1-2s)` lies in `[0, 4]`.
  have hfraction_nonneg : (0 : ℝ) ≤ 4 * s / (1 - 2 * s) :=
    div_nonneg (by linarith) hdelta_pos.le
  have hfraction_le : 4 * s / (1 - 2 * s) ≤ 2 := by
    rw [div_le_iff₀ hdelta_pos]
    linarith
  have hexponent_nonneg : (0 : ℝ) ≤ 2 + 4 * s / (1 - 2 * s) := by linarith
  have hexponent_le_four : 2 + 4 * s / (1 - 2 * s) ≤ 4 := by linarith
  -- The base `C/(1-2s)` is below the envelope base.
  have hCdiv_nonneg : (0 : ℝ) ≤ C / (1 - 2 * s) := div_nonneg hC hdelta_pos.le
  have hCdiv_le_base : C / (1 - 2 * s) ≤ max 1 (2 * C) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [div_le_iff₀ hdelta_pos]
    calc
      C = 2 * C * (1 / 2 : ℝ) := by ring
      _ ≤ 2 * C * (1 - 2 * s) := by
        exact mul_le_mul_of_nonneg_left hdelta_half (by linarith)
  have hCfactor :
      Real.rpow (C / (1 - 2 * s)) (2 + 4 * s / (1 - 2 * s)) ≤
        Real.rpow (max 1 (2 * C)) 4 :=
    (Real.rpow_le_rpow hCdiv_nonneg hCdiv_le_base hexponent_nonneg).trans
      (Real.rpow_le_rpow_of_exponent_le hbase_one hexponent_le_four)
  -- The factor `s^{-2s/(1-2s)}` is `exp` of a bounded quantity.
  have hnegMulLog_le_one : Real.negMulLog s ≤ 1 := by
    have hlog : 1 - s⁻¹ ≤ Real.log s := Real.one_sub_inv_le_log_of_pos hs
    have hmul := mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hs.le)
    calc
      Real.negMulLog s = (-s) * Real.log s := rfl
      _ ≤ (-s) * (1 - s⁻¹) := hmul
      _ = 1 - s := by
        field_simp
        ring
      _ ≤ 1 := by linarith
  have hcoef_nonneg : (0 : ℝ) ≤ 2 / (1 - 2 * s) := div_nonneg (by norm_num) hdelta_pos.le
  have hcoef_le_four : 2 / (1 - 2 * s) ≤ 4 := by
    rw [div_le_iff₀ hdelta_pos]
    linarith
  have hneg_exponent_le : 2 / (1 - 2 * s) * Real.negMulLog s ≤ 4 := by
    calc
      2 / (1 - 2 * s) * Real.negMulLog s ≤ 2 / (1 - 2 * s) * 1 :=
        mul_le_mul_of_nonneg_left hnegMulLog_le_one hcoef_nonneg
      _ ≤ 4 := by simpa using hcoef_le_four
  have hsfactor_eq :
      Real.rpow s (-(2 * s / (1 - 2 * s))) =
        Real.exp (2 / (1 - 2 * s) * Real.negMulLog s) := by
    change s ^ (-(2 * s / (1 - 2 * s))) = _
    rw [Real.rpow_def_of_pos hs]
    simp only [Real.negMulLog]
    congr 1
    field_simp
  have hsfactor : Real.rpow s (-(2 * s / (1 - 2 * s))) ≤ Real.exp 4 := by
    rw [hsfactor_eq]
    exact Real.exp_le_exp.mpr hneg_exponent_le
  calc
    Real.rpow (C / (1 - 2 * s)) (2 + 4 * s / (1 - 2 * s)) *
        Real.rpow s (-(2 * s / (1 - 2 * s))) ≤
        Real.rpow (max 1 (2 * C)) 4 * Real.exp 4 :=
      mul_le_mul hCfactor hsfactor (Real.rpow_nonneg hs.le _)
        (Real.rpow_nonneg hbase_nonneg _)
    _ = jBesovCaccioppoliEnvelope C := by
      rw [jBesovCaccioppoliEnvelope]; ring

/-- **The diagonal Caccioppoli prefactor on the manuscript range.**  For
`0 < s \le 1/4` the exact upstream prefactor at `t = s` is bounded by a scalar
depending only on its dimension-only Caccioppoli constant, times the three
factors displayed in the manuscript: the coarse ellipticity ratio raised to
`s/(1-2s)`, the coarse upper ellipticity `\Lambda_s`, and the scale weight
`3^{-2m}`. -/
theorem caccioppoliPrefactor_diag_le_jBesovEnvelope {d : ℕ} [NeZero d] (C : ℝ)
    (hC : 0 ≤ C) (Q : TriadicCube d) (a : Ch03.CoeffFamily d) {s : ℝ} (hs : 0 < s)
    (hs_quarter : s ≤ 1 / 4) :
    Ch03.caccioppoliPrefactor C Q a s s ≤
      jBesovCaccioppoliEnvelope C *
        (Real.rpow (Ch02.ThetaRatio Q s s a) (s / (1 - 2 * s)) *
          Ch02.LambdaS Q s a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))) := by
  have hdelta_eq : 1 - s - s = 1 - 2 * s := by ring
  have hscalar := caccioppoliScalarFactors_diag_le_jBesovEnvelope hC hs hs_quarter
  have htheta_nonneg : 0 ≤ Ch02.ThetaRatio Q s s a := Ch02.ThetaRatio_nonneg Q a hs hs
  have hlambda_nonneg : 0 ≤ Ch02.LambdaS Q s a :=
    Ch02.LambdaSq_finite_nonneg Q a hs le_rfl
  have hrest_nonneg :
      0 ≤ Real.rpow (Ch02.ThetaRatio Q s s a) (s / (1 - 2 * s)) *
          Ch02.LambdaS Q s a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg htheta_nonneg _) hlambda_nonneg)
      (Real.rpow_nonneg (by norm_num) _)
  rw [Ch03.caccioppoliPrefactor, hdelta_eq]
  calc
    Real.rpow (C / (1 - 2 * s)) (2 + 4 * s / (1 - 2 * s)) *
          Real.rpow s (-(2 * s / (1 - 2 * s))) *
          Real.rpow (Ch02.ThetaRatio Q s s a) (s / (1 - 2 * s)) *
          Ch02.LambdaS Q s a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) =
        Real.rpow (C / (1 - 2 * s)) (2 + 4 * s / (1 - 2 * s)) *
              Real.rpow s (-(2 * s / (1 - 2 * s))) *
            (Real.rpow (Ch02.ThetaRatio Q s s a) (s / (1 - 2 * s)) *
              Ch02.LambdaS Q s a *
              Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))) := by ring
    _ ≤
        jBesovCaccioppoliEnvelope C *
          (Real.rpow (Ch02.ThetaRatio Q s s a) (s / (1 - 2 * s)) *
            Ch02.LambdaS Q s a * Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hscalar hrest_nonneg

end

end Algsuperdiff.Section3.Provider.Besov
