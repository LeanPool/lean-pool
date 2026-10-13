/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseAssembly

/-!
# RootClauseBFinalArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `M`-uniform `dataOsc` weight -/

/-- `3^{-1/4} < 1`, so the uniform denominator is positive. -/
theorem one_sub_rpow_three_neg_quarter_pos :
    (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 4) : ℝ) := by
  have h : (3 : ℝ) ^ (-(1 / 4) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  linarith only [h]

/-- **The `γ`-gated cap on the Step-5 geometric ratio.**  `r₁ = 3^{-(1/2-γ)}` is
increasing in `γ`, so the regime clause `γ ≤ 1/4` — which the Step-6 producer's
own `γ ≤ 1/256` implies — pins it below `3^{-1/4}`. -/
theorem stepFiveRatioG_le_rpow_neg_quarter {M : ABKModel d} (hgamma : M.gamma ≤ 1 / 4) :
    stepFiveRatioG M ≤ (3 : ℝ) ^ (-(1 / 4) : ℝ) := by
  rw [stepFiveRatioG]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgamma])

/-- **The `M`-free `dataOsc` weight** `4C_δ/(1-3^{-1/4})`. -/
def rootClauseBOscWUniform (Cdel : ℝ) : ℝ :=
  4 * Cdel / (1 - (3 : ℝ) ^ (-(1 / 4) : ℝ))

theorem rootClauseBOscWUniform_nonneg {Cdel : ℝ} (hC : 0 ≤ Cdel) :
    0 ≤ rootClauseBOscWUniform Cdel := by
  rw [rootClauseBOscWUniform]
  exact div_nonneg (by linarith only [hC]) one_sub_rpow_three_neg_quarter_pos.le

/-- **The `M`-uniform funding enlargement.**  Inside the regime `γ ≤ 1/4` the
`dataOsc` weight is bounded by a constant free of the model. -/
theorem edFinalDataOscW_le_uniform {M : ABKModel d} {Cdel : ℝ}
    (hgamma : M.gamma < 1 / 2) (hquarter : M.gamma ≤ 1 / 4) (hC : 0 ≤ Cdel) :
    edFinalDataOscW M Cdel ≤ rootClauseBOscWUniform Cdel := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioG M := by
    linarith only [stepFiveRatioG_lt_one hgamma]
  have h2 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 4) : ℝ) :=
    one_sub_rpow_three_neg_quarter_pos
  have h3 : 1 - (3 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 - stepFiveRatioG M := by
    linarith only [stepFiveRatioG_le_rpow_neg_quarter hquarter]
  rw [edFinalDataOscW, rootClauseBOscWUniform]
  exact div_le_div_of_nonneg_left (by linarith only [hC]) h2 h3

/-! ## 2. The `α`-uniform `A6` cap constant -/

/-- **The `α`-free Step-1 amplitude** `ε₀ = (s/8)·√(1/2)`, the value of `stepOneEp`
at the top of the Step-1 window `δ ≤ 1/2`. -/
def stepOneEpUniform : ℝ := stepOneSEighth * Real.sqrt (1 / 2)

/-- **, the amplitude half**: `ε(δ) = (s/8)√δ ≤ (s/8)/√2` for every `δ` in the
Step-1 window. -/
theorem stepOneEp_le_stepOneEpUniform {delta : ℝ} (hdelta : delta ≤ 1 / 2) :
    stepOneEp delta ≤ stepOneEpUniform := by
  rw [stepOneEp, stepOneEpUniform]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdelta) stepOneSEighth_pos.le

/-- **The `α`-free `A6` cap constant** `2d((C·ε₀)²+1)`. -/
def rootClauseBCapsUniform (d : ℕ) (C : ℝ) : ℝ :=
  2 * (d : ℝ) * ((C * stepOneEpUniform) ^ 2 + 1)

theorem rootClauseBCapsUniform_nonneg (d : ℕ) (C : ℝ) :
    0 ≤ rootClauseBCapsUniform d C := by
  have h : (0 : ℝ) ≤ (C * stepOneEpUniform) ^ 2 := sq_nonneg _
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
    have hc : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith only [hc]
  rw [rootClauseBCapsUniform]
  exact mul_nonneg hd (by linarith only [h])

/-- **, the cap half**: the produced `A6` constant `2d((C·ε(δ))²+1)` is below its
value at the top of the Step-1 window, uniformly in `α`. -/
theorem capsConst_le_rootClauseBCapsUniform (d : ℕ) {C delta : ℝ} (hC : 0 ≤ C)
    (hdelta : delta ≤ 1 / 2) :
    2 * (d : ℝ) * ((C * stepOneEp delta) ^ 2 + 1) ≤ rootClauseBCapsUniform d C := by
  have hep0 : (0 : ℝ) ≤ C * stepOneEp delta := by
    refine mul_nonneg hC ?_
    rw [stepOneEp]
    exact mul_nonneg stepOneSEighth_pos.le (Real.sqrt_nonneg _)
  have hep : C * stepOneEp delta ≤ C * stepOneEpUniform :=
    mul_le_mul_of_nonneg_left (stepOneEp_le_stepOneEpUniform hdelta) hC
  have hsq : (C * stepOneEp delta) ^ 2 ≤ (C * stepOneEpUniform) ^ 2 :=
    pow_le_pow_left₀ hep0 hep 2
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) := by
    have hc : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith only [hc]
  rw [rootClauseBCapsUniform]
  exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hd

/-! ## 3. The four remaining monotone slots of the composite prefactor -/

/-- `rootClauseBCg` is monotone in its `C_Bc` slot. -/
theorem rootClauseBCg_mono_cbc (d : ℕ) {Ccacc Cosc CBc CBc' : ℝ} (hCcacc : 0 ≤ Ccacc)
    (hCosc : 0 ≤ Cosc) (h : CBc ≤ CBc') :
    rootClauseBCg d Ccacc Cosc CBc ≤ rootClauseBCg d Ccacc Cosc CBc' := by
  have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsqrt : Real.sqrt (256 / 63 * CBc) ≤ Real.sqrt (256 / 63 * CBc') :=
    Real.sqrt_le_sqrt (by linarith only [h])
  have hbr : Cosc * Real.sqrt (256 / 63 * CBc) + 1 ≤
      Cosc * Real.sqrt (256 / 63 * CBc') + 1 := by
    have := mul_le_mul_of_nonneg_left hsqrt hCosc
    linarith only [this]
  rw [rootClauseBCg, rootClauseBCg]
  exact mul_le_mul_of_nonneg_left hbr (mul_nonneg h1 hCcacc)

theorem rootClauseBCg_nonneg (d : ℕ) {Ccacc Cosc CBc : ℝ} (hCcacc : 0 ≤ Ccacc)
    (hCosc : 0 ≤ Cosc) : 0 ≤ rootClauseBCg d Ccacc Cosc CBc := by
  have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
    have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
    linarith only [h4]
  rw [rootClauseBCg]
  exact mul_nonneg (mul_nonneg h1 hCcacc) h3

/-- **The composite clause-(B) prefactor is monotone in its four data slots.**

`C_Bc` enters only through `rootClauseBCg`, `C_B` only through the bracket
`√(32/7 C_B) + 32/7 C_B`, and `C_WG`, `C_dM` only additively; all four are
monotone at the endpoint's own nonnegativity binders.  This is what lets the
`M`-uniform `C_WG` of §1 and the `α`-uniform `C_B` of §2 be substituted into
the funding hypothesis. -/
theorem rootClauseBPrefactor_mono_data (d : ℕ) [NeZero d]
    {Cch Ccacc Cosc CBc CBc' CB CB' Ctr CWG CWG' CdM CdM' : ℝ} (hCch : 0 ≤ Cch)
    (hCcacc : 0 ≤ Ccacc) (hCosc : 0 ≤ Cosc) (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr)
    (hCWG : 0 ≤ CWG) (hCdM : 0 ≤ CdM) (hBc : CBc ≤ CBc') (hB : CB ≤ CB')
    (hWG : CWG ≤ CWG') (hdM : CdM ≤ CdM') :
    rootClauseBPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CdM ≤
      rootClauseBPrefactor d Cch Ccacc Cosc CBc' CB' Ctr CWG' CdM' := by
  have hCg := rootClauseBCg_mono_cbc d hCcacc hCosc hBc
  have hCg0 : (0 : ℝ) ≤ rootClauseBCg d Ccacc Cosc CBc :=
    rootClauseBCg_nonneg d hCcacc hCosc
  have hCg0' : (0 : ℝ) ≤ rootClauseBCg d Ccacc Cosc CBc' :=
    rootClauseBCg_nonneg d hCcacc hCosc
  have hbrB : Real.sqrt (32 / 7 * CB) + 32 / 7 * CB ≤
      Real.sqrt (32 / 7 * CB') + 32 / 7 * CB' := by
    have hs : Real.sqrt (32 / 7 * CB) ≤ Real.sqrt (32 / 7 * CB') :=
      Real.sqrt_le_sqrt (by linarith only [hB])
    linarith only [hs, hB]
  have hbrB0 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
    have h5 := Real.sqrt_nonneg (32 / 7 * CB)
    linarith only [h5, hCB]
  have hXle : Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr ≤
      Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB') + 32 / 7 * CB')) * Ctr := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ ?_) hCtr
    · exact mul_le_mul_of_nonneg_left hbrB (by linarith only [hCch])
    · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) ?_) hCtr
    exact mul_nonneg (by linarith only [hCch]) hbrB0
  have hYle : Real.sqrt 4 * CWG + CdM ≤ Real.sqrt 4 * CWG' + CdM' := by
    have h := mul_le_mul_of_nonneg_left hWG (Real.sqrt_nonneg (4 : ℝ))
    linarith only [h, hdM]
  have hYnn : (0 : ℝ) ≤ Real.sqrt 4 * CWG + CdM := by
    have h6 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWG
    linarith only [h6, hCdM]
  have hleft : rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
        (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
          stepSevenBridgeConst stepSevenCgS *
          (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) ≤
      rootClauseBCg d Ccacc Cosc CBc' * Real.sqrt 4 *
        (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
          stepSevenBridgeConst stepSevenCgS *
          (Cch * 64 * (Real.sqrt (32 / 7 * CB') + 32 / 7 * CB')) * Ctr) := by
    refine mul_le_mul ?_ hXle hXnn ?_
    · exact mul_le_mul_of_nonneg_right hCg (Real.sqrt_nonneg 4)
    · exact mul_nonneg hCg0' (Real.sqrt_nonneg 4)
  have hright : rootClauseBCg d Ccacc Cosc CBc * (Real.sqrt 4 * CWG + CdM) ≤
      rootClauseBCg d Ccacc Cosc CBc' * (Real.sqrt 4 * CWG' + CdM') :=
    mul_le_mul hCg hYle hYnn hCg0'
  rw [rootClauseBPrefactor, rootClauseBPrefactor]
  exact add_le_add hleft hright

/-! ## 4. The `γ|log γ|²` thresholds -/

/-- `|log γ| ≤ 8 γ^{-1/8}` on `(0,1]`, from `log x ≤ x - 1` at `x = γ^{-1/8}`. -/
theorem abs_log_le_rpow_neg_eighth {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    |Real.log g| ≤ 8 * g ^ (-(1 / 8) : ℝ) := by
  have hpow : (0 : ℝ) < g ^ (-(1 / 8) : ℝ) := Real.rpow_pos_of_pos hg0 _
  have hlog : Real.log (g ^ (-(1 / 8) : ℝ)) ≤ g ^ (-(1 / 8) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpow
  have hrw : Real.log (g ^ (-(1 / 8) : ℝ)) = -(1 / 8 : ℝ) * Real.log g :=
    Real.log_rpow hg0 _
  have hlog0 : Real.log g ≤ 0 := Real.log_nonpos hg0.le hg1
  have habs : |Real.log g| = -Real.log g := abs_of_nonpos hlog0
  rw [hrw] at hlog
  rw [habs]
  linarith only [hlog, hpow]

/-- **The elementary `γ|log γ|²` bound.**  For `0 < γ ≤ 1`, `γ|log γ|² ≤ 64
γ^{3/4}`. -/
theorem gamma_mul_log_sq_le {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    g * |Real.log g| ^ (2 : ℕ) ≤ 64 * g ^ (3 / 4 : ℝ) := by
  have hb := abs_log_le_rpow_neg_eighth hg0 hg1
  have hsq : |Real.log g| ^ (2 : ℕ) ≤ (8 * g ^ (-(1 / 8) : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hsplit8 : g ^ (-(1 / 4) : ℝ) = g ^ (-(1 / 8) : ℝ) * g ^ (-(1 / 8) : ℝ) := by
    rw [← Real.rpow_add hg0]
    norm_num
  have hid : (8 * g ^ (-(1 / 8) : ℝ)) ^ (2 : ℕ) =
      64 * g ^ (-(1 / 4) : ℝ) := by
    rw [mul_pow, hsplit8]
    ring
  have hgid : g * g ^ (-(1 / 4) : ℝ) = g ^ (3 / 4 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one g]
    rw [← Real.rpow_add hg0]
    norm_num
  calc g * |Real.log g| ^ (2 : ℕ)
      ≤ g * (8 * g ^ (-(1 / 8) : ℝ)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hsq hg0.le
    _ = 64 * (g * g ^ (-(1 / 4) : ℝ)) := by rw [hid]; ring
    _ = 64 * g ^ (3 / 4 : ℝ) := by rw [hgid]

/-- **The `α`-free gate.**  `γ ≤ (A/64)^{4/3}` funds `γ|log γ|² ≤ A`. -/
theorem gamma_log_sq_le_of_le_threshold {g A : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hA : 0 < A) (h : g ≤ (A / 64) ^ (4 / 3 : ℝ)) :
    g * |Real.log g| ^ (2 : ℕ) ≤ A := by
  have hAq : (0 : ℝ) ≤ A / 64 := by linarith only [hA]
  have hstep : g ^ (3 / 4 : ℝ) ≤ ((A / 64) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hg0.le h (by norm_num)
  have hprod : (4 / 3 : ℝ) * (3 / 4 : ℝ) = 1 := by norm_num
  have hcomp : ((A / 64) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) = A / 64 := by
    rw [← Real.rpow_mul hAq, hprod, Real.rpow_one]
  have hfinal : g ^ (3 / 4 : ℝ) ≤ A / 64 := by rw [← hcomp]; exact hstep
  have hmain := gamma_mul_log_sq_le hg0 hg1
  have h64 : 64 * g ^ (3 / 4 : ℝ) ≤ 64 * (A / 64) :=
    mul_le_mul_of_nonneg_left hfinal (by norm_num)
  linarith only [hmain, h64]

/-- **The `α`-dependent gate.**  `γ ≤ (B/64)²` funds `γ|log γ|² ≤ B·γ^{1/4}` — the
shape the Step-1 amplitude `ε(δ) ≥ c·γ^{1/4}` (a consequence of the root's own
`α`-range `α ≤ 1 - C√γ`) consumes. -/
theorem gamma_log_sq_le_rpow_quarter {g B : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hB : 0 < B) (h : g ≤ (B / 64) ^ (2 : ℕ)) :
    g * |Real.log g| ^ (2 : ℕ) ≤ B * g ^ (1 / 4 : ℝ) := by
  have hsplit : g ^ (3 / 4 : ℝ) =
      g ^ (1 / 2 : ℝ) * g ^ (1 / 4 : ℝ) := by
    have hadd := Real.rpow_add hg0 (1 / 2 : ℝ) (1 / 4 : ℝ)
    have h2 : (1 / 2 : ℝ) + (1 / 4 : ℝ) = 3 / 4 := by norm_num
    rw [h2] at hadd
    exact hadd
  have hsqrt : g ^ (1 / 2 : ℝ) ≤ B / 64 := by
    rw [← Real.sqrt_eq_rpow]
    have hs : Real.sqrt g ≤ Real.sqrt ((B / 64) ^ (2 : ℕ)) := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by linarith only [hB])] at hs
  have hq0 : (0 : ℝ) ≤ g ^ (1 / 4 : ℝ) := (Real.rpow_pos_of_pos hg0 _).le
  have hmain := gamma_mul_log_sq_le hg0 hg1
  have hstep : 64 * g ^ (3 / 4 : ℝ) ≤ B * g ^ (1 / 4 : ℝ) := by
    rw [hsplit]
    have h1 : 64 * (g ^ (1 / 2 : ℝ) * g ^ (1 / 4 : ℝ)) =
        (64 * g ^ (1 / 2 : ℝ)) * g ^ (1 / 4 : ℝ) := by ring
    have h2 : 64 * g ^ (1 / 2 : ℝ) ≤ B := by
      have := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 64)
      linarith only [this]
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 hq0
  linarith only [hmain, hstep]

end

end Algsuperdiff.Section4.Provider.Regularity
