/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBPayload
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccMatching

/-!
# RootPayloadCest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The sample-free cap on the Caccioppoli constant -/

/-- **The `ω`-free Caccioppoli constant** of the §4.4 clause-(B) chain:
`√((2·max{1,C})⁴ · 4 · ((16384/441)·C_B²)²)`.

This is `StepSevenCaccMatching.stepSevenCaccPrefactor_le` evaluated at the `Θ`
cap `StepSevenLambdaSlots.stepSevenThetaRatio_le_of_caps` produces from the
`A6` clause-(B) record, then square-rooted.  It mentions neither the sample,
nor the model, nor the scale. -/
def rootClauseBCaccUniform (C CB : ℝ) : ℝ :=
  Real.sqrt ((2 * max 1 C) ^ (4 : ℕ) * 4 * (16384 / 441 * CB ^ (2 : ℕ)) ^ (2 : ℕ))

theorem rootClauseBCaccUniform_nonneg (C CB : ℝ) : 0 ≤ rootClauseBCaccUniform C CB :=
  Real.sqrt_nonneg _

/-- **The `C_est` uniformization, at the level of the Caccioppoli constant.**

For every coefficient family satisfying the `A6` clause-(B) caps on `□_{k+1}`
against ANY positive comparator, the Caccioppoli constant on the child `□_k` is
bounded by the sample-free `rootClauseBCaccUniform`.  The comparator `sigma`
cancels inside `stepSevenThetaRatio_le_of_caps` — this is why the bound is
`σ`-free as well. -/
theorem stepSevenCaccConst_le_uniform [NeZero d] {k : ℤ} {a : CoeffFamily d}
    {C sigma CB : ℝ} (hC : 0 < C) (hsigma : 0 < sigma)
    (hcaps : StepSevenLambdaCaps (originCube d (k + 1)) a sigma CB) :
    stepSevenCaccConst C (originCube d k) a ≤ rootClauseBCaccUniform C CB := by
  have hidx : (k + 1 - 1 : ℤ) = k := by ring
  have hTheta :
      Ch02.ThetaRatio (originCube d k) stepSevenCaccS stepSevenCaccT a ≤
        16384 / 441 * CB ^ (2 : ℕ) := by
    have h := stepSevenThetaRatio_le_of_caps (k := k + 1) a hsigma hcaps
    rwa [hidx] at h
  have hpref := stepSevenCaccPrefactor_le (Q := originCube d k) (a := a) hC hTheta
  rw [stepSevenCaccConst, rootClauseBCaccUniform]
  exact Real.sqrt_le_sqrt hpref

/-! ## 2. Monotonicity of the composite prefactor in its `C_cacc` slot -/

/-- `rootClauseBCg` is monotone in `C_cacc`: it is `3^{3d+1/4}·C_cacc·(…)` with
both cofactors nonnegative. -/
theorem rootClauseBCg_mono_ccacc (d : ℕ) {Ccacc Ccacc' Cosc CBc : ℝ}
    (hCosc : 0 ≤ Cosc) (h : Ccacc ≤ Ccacc') :
    rootClauseBCg d Ccacc Cosc CBc ≤ rootClauseBCg d Ccacc' Cosc CBc := by
  have h1 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have h3 : (0 : ℝ) ≤ Cosc * Real.sqrt (256 / 63 * CBc) + 1 := by
    have h4 := mul_nonneg hCosc (Real.sqrt_nonneg (256 / 63 * CBc))
    linarith only [h4]
  rw [rootClauseBCg, rootClauseBCg]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h h1) h3

/-- **The composite clause-(B) prefactor is monotone in `C_cacc`.**  The two sign
conditions on the brackets are exactly the endpoint's own nonnegativity
binders. -/
theorem rootClauseBPrefactor_mono_ccacc (d : ℕ) [NeZero d]
    {Cch Ccacc Ccacc' Cosc CBc CB Ctr CWG CdM : ℝ} (hCch : 0 ≤ Cch)
    (hCosc : 0 ≤ Cosc) (hCB : 0 ≤ CB) (hCtr : 0 ≤ Ctr) (hCWG : 0 ≤ CWG)
    (hCdM : 0 ≤ CdM) (h : Ccacc ≤ Ccacc') :
    rootClauseBPrefactor d Cch Ccacc Cosc CBc CB Ctr CWG CdM ≤
      rootClauseBPrefactor d Cch Ccacc' Cosc CBc CB Ctr CWG CdM := by
  have hCg := rootClauseBCg_mono_ccacc d (Cosc := Cosc) (CBc := CBc) hCosc h
  have hXnn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
      stepSevenBridgeConst stepSevenCgS *
      (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr := by
    have hb : (0 : ℝ) ≤ Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB) := by
      have h1 : (0 : ℝ) ≤ Cch * 64 := by linarith only [hCch]
      have h2 : (0 : ℝ) ≤ Real.sqrt (32 / 7 * CB) + 32 / 7 * CB := by
        have h5 := Real.sqrt_nonneg (32 / 7 * CB)
        linarith only [h5, hCB]
      exact mul_nonneg h1 h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (stepSevenEmbeddingConst_nonneg d)) (stepSevenBridgeConst_nonneg _)) hb) hCtr
  have hYnn : (0 : ℝ) ≤ Real.sqrt 4 * CWG + CdM := by
    have h6 := mul_nonneg (Real.sqrt_nonneg (4 : ℝ)) hCWG
    linarith only [h6, hCdM]
  have hleft : rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) ≤
      rootClauseBCg d Ccacc' Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCg (Real.sqrt_nonneg 4)) hXnn
  have hright : rootClauseBCg d Ccacc Cosc CBc * (Real.sqrt 4 * CWG + CdM) ≤
      rootClauseBCg d Ccacc' Cosc CBc * (Real.sqrt 4 * CWG + CdM) :=
    mul_le_mul_of_nonneg_right hCg hYnn
  rw [rootClauseBPrefactor, rootClauseBPrefactor]
  exact add_le_add hleft hright

end

end Algsuperdiff.Section4.Provider.Regularity
