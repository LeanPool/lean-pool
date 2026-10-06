/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseImbalanceComparison

/-!
# High-contrast homogenization: Entry.Response.Core.ResponseCalibrationBundles

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Calibration and source smallness from the raw output

This file derives two of the hypothesis bundles that `adapted_response_core` is assembled from,
directly from the raw multiscale output `RawOutput`: `response_calibrated_blocks`
(`e.response.calibrated.blocks`) produces the calibration bundle `RespCalibrated` from the Riccati
identity and the response-imbalance comparison, and `response_source_smallness`
(`e.response.source.smallness`) produces a source-smallness constant `Bresp` from the two-grid
source normalization and the scale-decay estimate. It also carries the load-quadratic identities —
`respLsqMinus`/`Plus`, `respEJMinus`/`Plus`, `respTauMinus`, and the pairings of the response load
vectors against `respP` — that later files in the chain need.
-/

section
open HCPolySupport.HighContrast (CoeffSpace aspectRatio matSqrt toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-- `e.response.calibrated.blocks`.  The constant
depends only on `(d, γ)`, never on the law, `F`, `E`, `Pi` or `σ`.

Route: the Riccati identity `GeometricMean.geoMean_riccati` gives `M(E) <= E <= d(E)^{1/2} M(E)`
(`p.response.transfer`); then `raw.calib_lo`/`raw.calib_hi` at `s`, the comparison `E_t <= E_s <=
r E_t`
of `response_imbalance_comparison`, and `GeometricMean.geoMean_mono`.  The congruence cost is
`sqrt(r(1+xi)/(1-xi)) <= C(d)` because `xi <= 1/2` and `r < e^{d/2}` ; `D`
commutes with `M_0`.

The premises `_hε`, `_hσ` are carried: without them `1 ≤ B` and `jStar ≤ s`
are unavailable.  The binder *names* are underscore-prefixed because they do not
occur in the statement's own type; the hypotheses are unchanged and the proof uses them
(with no linter suppression). -/
theorem response_calibrated_blocks (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated C P jStar F s t := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨he0, he1⟩ := S.eps0_mem
  have hs1 : Real.sqrt S.eps0 < 1 := by
    have hx := Real.sqrt_lt_sqrt he0.le he1
    rwa [Real.sqrt_one] at hx
  have hx0pos : 0 < Real.sqrt S.eps0 * S.eps0 := mul_pos (Real.sqrt_pos.mpr he0) he0
  have hx0lt : Real.sqrt S.eps0 * S.eps0 < 1 := by
    calc Real.sqrt S.eps0 * S.eps0 ≤ Real.sqrt S.eps0 * 1 :=
          mul_le_mul_of_nonneg_left he1.le (Real.sqrt_nonneg _)
      _ = Real.sqrt S.eps0 := mul_one _
      _ < 1 := hs1
  have hden : 0 < 1 - Real.sqrt S.eps0 * S.eps0 := by linarith only [hx0lt]
  have hexp1 : (1 : ℝ) ≤ Real.exp (d : ℝ) := Real.one_le_exp (by positivity)
  have hCpos : 0 < Real.sqrt ((1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
      (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt ((1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
    (1 - Real.sqrt S.eps0 * S.eps0)⁻¹), hCpos, ?_⟩
  intro ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw
  have := raw.prob
  -- scalars
  have hξpos : 0 < Real.sqrt ε * σ := mul_pos (Real.sqrt_pos.mpr hε.1) hσ.1
  have hξle : Real.sqrt ε * σ ≤ Real.sqrt S.eps0 * S.eps0 :=
    mul_le_mul (Real.sqrt_le_sqrt hε.2) (le_trans hσ.2 hε.2) hσ.1.le (Real.sqrt_nonneg _)
  have hξden : 0 < 1 - Real.sqrt ε * σ := by linarith only [hξle, hx0lt]
  have hinvle : (1 - Real.sqrt ε * σ)⁻¹ ≤ (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ := by
    have h := one_div_le_one_div_of_le hden
      (show 1 - Real.sqrt S.eps0 * S.eps0 ≤ 1 - Real.sqrt ε * σ by linarith only [hξle])
    rwa [one_div, one_div] at h
  -- imbalance comparison
  obtain ⟨hk1, hkts, -, hr1, hrlt⟩ := response_imbalance_comparison d _hd γ _hγ S _hS ε σ hε hσ
    Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw
  have hrexp : respRatio P jStar F s t ≤ Real.exp (d : ℝ) := by
    refine hrlt.le.trans (Real.exp_le_exp.mpr ?_)
    have hσ1 : σ ≤ 1 := le_trans hσ.2 (le_trans hε.2 he1.le)
    calc (d : ℝ) * σ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hσ1 (Nat.cast_nonneg d)
      _ = (d : ℝ) := mul_one _
  have habC : Real.sqrt ((1 + Real.sqrt ε * σ) *
        ((1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t))
      ≤ Real.sqrt ((1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
        (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) := by
    refine Real.sqrt_le_sqrt ?_
    have hmid : (1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t ≤
        (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ * Real.exp (d : ℝ) :=
      mul_le_mul hinvle hrexp (by linarith only [hr1]) (by positivity)
    calc (1 + Real.sqrt ε * σ) * ((1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t)
        ≤ (1 + Real.sqrt S.eps0 * S.eps0) *
            ((1 - Real.sqrt S.eps0 * S.eps0)⁻¹ * Real.exp (d : ℝ)) := by
          refine mul_le_mul (by linarith only [hξle]) hmid ?_ (by linarith only [hx0pos])
          positivity
      _ = (1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
            (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ := by ring
  have hbaC : Real.sqrt (((1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t) *
        (1 + Real.sqrt ε * σ))
      ≤ Real.sqrt ((1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
        (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) := by
    rw [mul_comm]; exact habC
  have hcsC : Real.sqrt ((1 + Real.sqrt ε * σ) * (1 - Real.sqrt ε * σ)⁻¹)
      ≤ Real.sqrt ((1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
        (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) := by
    refine Real.sqrt_le_sqrt ?_
    have h1 : (1 + Real.sqrt ε * σ) * (1 - Real.sqrt ε * σ)⁻¹ ≤
        (1 + Real.sqrt S.eps0 * S.eps0) * (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ := by
      refine mul_le_mul (by linarith only [hξle]) hinvle (by positivity) (by linarith only [hx0pos])
    have h2 : (0 : ℝ) ≤ (1 + Real.sqrt S.eps0 * S.eps0) * (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ := by
      positivity
    calc (1 + Real.sqrt ε * σ) * (1 - Real.sqrt ε * σ)⁻¹
        ≤ ((1 + Real.sqrt S.eps0 * S.eps0) * (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) * 1 := by
          rw [mul_one]; exact h1
      _ ≤ ((1 + Real.sqrt S.eps0 * S.eps0) * (1 - Real.sqrt S.eps0 * S.eps0)⁻¹) *
            Real.exp (d : ℝ) := mul_le_mul_of_nonneg_left hexp1 h2
      _ = (1 + Real.sqrt S.eps0 * S.eps0) * Real.exp (d : ℝ) *
            (1 - Real.sqrt S.eps0 * S.eps0)⁻¹ := by ring
  -- matrix data
  have hAf : (toFullBlockMat F).PosDef := posDef_toFullBlockMat raw.symm raw.pos
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hAt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm t
  have hAs : (toFullBlockMat (respMean P jStar F s)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm s
  have hBt := respCalib_swapConj_posDef hAt
  have hBs := respCalib_swapConj_posDef hAs
  have hBf := respCalib_swapConj_posDef hAf
  have hsharp : ∀ u : ℤ, toFullBlockMat (blockSwap d) *
      (toFullBlockMat (respMean P jStar F u))⁻¹ * toFullBlockMat (blockSwap d) ≤
      toFullBlockMat (respMean P jStar F u) := by
    intro u
    have hpos := Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm u
    have hswap := Analysis.adaptedMean_swapConj_le _hd P γ E Ψ Kg Src raw.stat raw.ell jStar
      raw.hj (explicitCanonicalMetric F) hm u
    have hh : (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (respMean P jStar F u))⁻¹ *
        toFullBlockMat (blockSwap d)))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using!
        (respCalib_swapConj_posDef hpos).isHermitian
    have hle := Analysis.matrixOrder_of_blockMatLoewnerLE hh hpos.isHermitian hswap
    simpa only [toFullBlockMat_ofFullBlockMat] using! hle
  have hcal_hi : toFullBlockMat (respMean P jStar F s) ≤
      (1 + Real.sqrt ε * σ) • toFullBlockMat F := by
    have h := Analysis.matrixOrder_of_blockMatLoewnerLE hAs.isHermitian
      ((Analysis.toFullBlockMat_isHermitian_iff _).2 (isSymmetricBlockMat_blockScale _ raw.symm)) raw.calib_hi
    rwa [toFullBlockMat_blockScale] at h
  have hcal_lo : (1 - Real.sqrt ε * σ) • toFullBlockMat F ≤
      toFullBlockMat (respMean P jStar F s) := by
    have h := Analysis.matrixOrder_of_blockMatLoewnerLE
      ((Analysis.toFullBlockMat_isHermitian_iff _).2 (isSymmetricBlockMat_blockScale _ raw.symm))
      hAs.isHermitian raw.calib_lo
    rwa [toFullBlockMat_blockScale] at h
  have hjs : (jStar : ℤ) ≤ s := le_of_lt (jStar_lt_s_of_raw d _hd γ _hγ S ε σ Cglob Cprof Csrc
    Bresp hε hσ H P E Ψ Kg Src B jStar F s t raw)
  have hts : toFullBlockMat (respMean P jStar F t) ≤ toFullBlockMat (respMean P jStar F s) :=
    Analysis.matrixOrder_of_blockMatLoewnerLE hAt.isHermitian hAs.isHermitian
      (Annealed.adaptedMean_antitone d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm s t hjs raw.hst.le)
  have hdet : toFullBlockMat (respMean P jStar F s) ≤
      respRatio P jStar F s t • toFullBlockMat (respMean P jStar F t) :=
    respCalib_le_detRatio_smul hAt hAs hts
  have hinvnn : (0 : ℝ) ≤ (1 - Real.sqrt ε * σ)⁻¹ := inv_nonneg.mpr hξden.le
  have hA1 : toFullBlockMat (respMean P jStar F t) ≤
      (1 + Real.sqrt ε * σ) • toFullBlockMat F := hts.trans hcal_hi
  have hA2 : toFullBlockMat F ≤
      ((1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t) •
        toFullBlockMat (respMean P jStar F t) := by
    have hsc := smul_le_smul_left (c := (1 - Real.sqrt ε * σ)⁻¹) hinvnn (hcal_lo.trans hdet)
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ hξden.ne', one_smul] at hsc
  have hA2s : toFullBlockMat F ≤
      (1 - Real.sqrt ε * σ)⁻¹ • toFullBlockMat (respMean P jStar F s) := by
    have hsc := smul_le_smul_left (c := (1 - Real.sqrt ε * σ)⁻¹) hinvnn hcal_lo
    rwa [smul_smul, inv_mul_cancel₀ hξden.ne', one_smul] at hsc
  have hapos : (0 : ℝ) < 1 + Real.sqrt ε * σ := by linarith only [hξpos]
  have hbpos : (0 : ℝ) < (1 - Real.sqrt ε * σ)⁻¹ * respRatio P jStar F s t :=
    mul_pos (inv_pos.mpr hξden) (by linarith only [hr1])
  have hNt := respCalib_canonicalMean_le hAt hAf hapos hbpos hA1 hA2
  have hNf := respCalib_canonicalMean_le hAf hAt hbpos hapos hA2 hA1
  have hNs := respCalib_canonicalMean_le hAs hAf hapos (inv_pos.mpr hξden) hcal_hi hA2s
  have hkt : (0 : ℝ) < respKappa P jStar F t := by linarith only [hk1]
  have hks : (0 : ℝ) < respKappa P jStar F s := by linarith only [hk1, hkts]
  have hNtA := respCalib_geoMean_le_left hAt hBt (hsharp t)
  have hAtN := respCalib_le_sqrt_smul_geoMean hAt hBt hkt (le_of_imbalance_le hAt le_rfl)
  have hAsN := respCalib_le_sqrt_smul_geoMean hAs hBs hks (le_of_imbalance_le hAs le_rfl)
  have hGM : (toFullBlockMat (respG F))ᵀ *
      GeometricMean.geoMean (toFullBlockMat F) (toFullBlockMat (blockSwap d) *
        (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)) *
      toFullBlockMat (respG F) = toFullBlockMat (respM0 F) := by
    rw [← respCalib_canonicalMean_full F]
    exact respCalib_congr_canonicalMean hAf
  have hM0psd : (toFullBlockMat (respM0 F)).PosSemidef := by
    rw [← hGM]
    have hx := (GeometricMean.geoMeanPosDef hAf hBf).posSemidef.conjTranspose_mul_mul_same
      (toFullBlockMat (respG F))
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hx
  have hlow := respCalib_lower (GeometricMean.geoMeanPosDef hAt hBt).posSemidef hGM hCpos hbaC hNf hNtA
  have hupt := respCalib_upper hM0psd hGM (Real.sqrt_nonneg (respKappa P jStar F t)) habC
    hAtN hNt
  have hups := respCalib_upper hM0psd hGM (Real.sqrt_nonneg (respKappa P jStar F s)) hcsC
    hAsN hNs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatMinus_full]
    exact hlow
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatPlus_full, respCalib_ehatMinus_full]
    have hD := Analysis.matrix_congr_le hlow (toFullBlockMat (blockD d))
    rwa [Matrix.mul_smul, Matrix.smul_mul, respCalib_blockD_congr_respM0] at hD
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatMinus_full]
    exact hupt
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatPlus_full, respCalib_ehatMinus_full]
    have hD := Analysis.matrix_congr_le hupt (toFullBlockMat (blockD d))
    rwa [Matrix.mul_smul, Matrix.smul_mul, respCalib_blockD_congr_respM0] at hD
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatMinus_full]
    exact hups
  · refine HCPolySupport.HighContrast.blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, respCalib_ehatPlus_full, respCalib_ehatMinus_full]
    have hD := Analysis.matrix_congr_le hups (toFullBlockMat (blockD d))
    rwa [Matrix.mul_smul, Matrix.smul_mul, respCalib_blockD_congr_respM0] at hD

/-! ## The source smallness estimate -/

/-- `e.response.source.smallness`:
`C Pi e(m)^2 3^{-rho_max(t-j_*)} <= eta^{1/Q}` and `C Pi e(m)^2 3^{-3(s-j_*)/2} <= 1`, once
`B_resp` is large enough.  `B_resp` is chosen after `H`, `eta`, `sigma` and `C_glob`, exactly
the printed order (`e.response.source.smallness`).

Route: `raw.hsrc` and `Annealed.adaptedMean_refBlock_normalization`
(`e.two.grid.source.normalization`, `e.two.grid.source.normalization`) supply `Csrc` and the
envelope constant; `raw.ecc`
(`e.global.selection.eccentricity`, `e.global.selection.eccentricity`) bounds `e(m)^2` by
`(2+Pi)^{2 Cglob}`; `raw.hs_lo`
and `raw.ht_hi` (`e.global.selection.scales`, `e.global.selection.scales`) with
`scale_decay_of_hs_lo` turn
`3^{-rho(u-j_*)}` into `(2+Pi)^{-rho B}`, and `exists_Bresp_of_decay` then produces
`Bresp`.  `raw.hB` gives `Bresp <= B`, and `1 <= aspectRatio E` comes from
`Analysis.one_le_aspectRatio`. -/
theorem response_source_smallness (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δad : ℝ, δad ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ H : ℕ, max 4 S.h ≤ H →
      ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
      ∀ Cprof : ℝ, 0 < Cprof →
      ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
      ∀ Cglob : ℝ, 0 < Cglob →
        ∃ Bresp : ℝ, 1 ≤ Bresp ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespSourceSmall d γ C η E F jStar s t := by
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro ε _hε δad _hδad H _hH η hη Cprof _hCprof σ _hσ Cglob hCglob
  -- Step 1: positivity of ρ := rhoMax d γ
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ _hγ
  have hQpos : (0 : ℝ) < (bigQ d γ : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hQ2
  have hργ : (0:ℝ) ≤ γ := _hγ.1
  have hγlt1 : γ < 1 := _hγ.2
  have hdpos : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  have hρ : (0:ℝ) < rhoMax d γ := by
    have hbracket : (0:ℝ) < (d:ℝ) + (1 - γ) / 4 := by
      have : (0:ℝ) < (1 - γ) / 4 := by linarith only [hγlt1]
      linarith only [hdpos, this]
    have hterm : (0:ℝ) < (bigQ d γ : ℝ)⁻¹ * ((d:ℝ) + (1 - γ) / 4) :=
      mul_pos (inv_pos.mpr hQpos) hbracket
    unfold rhoMax
    linarith only [hργ, hterm]
  have hη0 : (0:ℝ) < η := hη.1
  -- Step 2: two applications of exists_Bresp_of_decay
  have hτ1 : (0:ℝ) < η ^ ((1:ℝ) / (bigQ d γ : ℝ)) :=
    Real.rpow_pos_of_pos hη0 _
  obtain ⟨Bresp1, hBresp1_ge, hBresp1⟩ :=
    exists_Bresp_of_decay 1 Cglob (rhoMax d γ) (η ^ ((1:ℝ) / (bigQ d γ : ℝ)))
      one_pos hCglob hρ hτ1
  obtain ⟨Bresp2, hBresp2_ge, hBresp2⟩ :=
    exists_Bresp_of_decay 1 Cglob (3/2 : ℝ) 1 one_pos hCglob (by norm_num) one_pos
  refine ⟨max Bresp1 Bresp2, le_trans hBresp1_ge (le_max_left _ _), ?_⟩
  intro P E Ψ Kg Src B jStar F s t raw
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  obtain ⟨hPivalpos, hPivalge3⟩ :=
    HCPolySupport.HighContrast.Annealed.aspectRatio_pos_and_three_le raw.ell
  set Pival : ℝ := aspectRatio E with hPivaldef
  set X : ℝ := ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ with hXdef
  have hXnonneg : 0 ≤ X := by positivity
  have hPpos : (0:ℝ) < 2 + Pival := by linarith only [hPivalpos]
  have hB_ge : max Bresp1 Bresp2 ≤ B := le_trans (le_max_right _ _) raw.hB
  have hB1 : Bresp1 ≤ B := le_trans (le_max_left _ _) hB_ge
  have hB2 : Bresp2 ≤ B := le_trans (le_max_right _ _) hB_ge
  constructor
  · -- first conjunct: exponent ρ := rhoMax d γ, τ := η^(1/Q)
    have hs_le_t : (jStar:ℤ) + ⌈B * Real.logb 3 (2 + Pival)⌉ ≤ t :=
      le_trans raw.hs_lo (by have := raw.hst; omega)
    have hdecay := scale_decay_of_hs_lo jStar t B Pival (rhoMax d γ) hPivalge3 hρ.le hs_le_t
    have hchain1 := hBresp1 B Pival hB1 hPivalge3
    rw [one_mul] at hchain1
    -- X ≤ (2+Pival)^(2*Cglob)
    have hXsq : X ≤ (2 + Pival) ^ (2 * Cglob) := by
      have hecc := raw.ecc
      have hXhalf_nonneg : 0 ≤ X ^ ((1:ℝ)/2) := Real.rpow_nonneg hXnonneg _
      have hstep1 : (X ^ ((1:ℝ)/2)) ^ (2:ℝ) ≤ ((2 + Pival) ^ Cglob) ^ (2:ℝ) :=
        Real.rpow_le_rpow hXhalf_nonneg hecc (by norm_num)
      have hXeq : (X ^ ((1:ℝ)/2)) ^ (2:ℝ) = X := by
        rw [← Real.rpow_mul hXnonneg, show (1:ℝ)/2*2 = 1 by norm_num, Real.rpow_one]
      have hRHSeq : ((2 + Pival) ^ Cglob) ^ (2:ℝ) = (2 + Pival) ^ (2 * Cglob) := by
        rw [← Real.rpow_mul hPpos.le]
        congr 1
        ring
      rw [hXeq, hRHSeq] at hstep1
      exact hstep1
    -- Pival ≤ (2+Pival)^1
    have hPivalle : Pival ≤ (2 + Pival) ^ (1:ℝ) := by
      rw [Real.rpow_one]; linarith only []
    have h3le : (3:ℝ) ^ (-(rhoMax d γ * ((t:ℝ) - (jStar:ℝ)))) ≤ (2 + Pival) ^ (-(rhoMax d γ * B)) :=
      hdecay
    have step_a : Pival * X ≤ (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) :=
      mul_le_mul hPivalle hXsq hXnonneg (Real.rpow_nonneg hPpos.le 1)
    have step_b : Pival * X * (3:ℝ) ^ (-(rhoMax d γ * ((t:ℝ) - (jStar:ℝ)))) ≤
        (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-(rhoMax d γ * B)) :=
      mul_le_mul step_a h3le (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)
        (mul_nonneg (Real.rpow_nonneg hPpos.le 1) (Real.rpow_nonneg hPpos.le (2 * Cglob)))
    have hcomb : (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-(rhoMax d γ * B))
        = (2 + Pival) ^ (1 + 2 * Cglob - rhoMax d γ * B) := by
      rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
      congr 1
    calc
      (1:ℝ) * Pival * X * (3:ℝ) ^ (-(rhoMax d γ * ((t:ℝ) - (jStar:ℝ))))
          = Pival * X * (3:ℝ) ^ (-(rhoMax d γ * ((t:ℝ) - (jStar:ℝ)))) := by rw [one_mul]
      _ ≤ (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-(rhoMax d γ * B)) :=
          step_b
      _ = (2 + Pival) ^ (1 + 2 * Cglob - rhoMax d γ * B) := hcomb
      _ ≤ η ^ ((1:ℝ) / (bigQ d γ : ℝ)) := hchain1
  · -- second conjunct: exponent (3:ℝ)/2, τ := 1
    have hdecay2 := scale_decay_of_hs_lo jStar s B Pival (3/2:ℝ) hPivalge3 (by norm_num) raw.hs_lo
    have hchain2 := hBresp2 B Pival hB2 hPivalge3
    rw [one_mul] at hchain2
    have hXsq : X ≤ (2 + Pival) ^ (2 * Cglob) := by
      have hecc := raw.ecc
      have hXhalf_nonneg : 0 ≤ X ^ ((1:ℝ)/2) := Real.rpow_nonneg hXnonneg _
      have hstep1 : (X ^ ((1:ℝ)/2)) ^ (2:ℝ) ≤ ((2 + Pival) ^ Cglob) ^ (2:ℝ) :=
        Real.rpow_le_rpow hXhalf_nonneg hecc (by norm_num)
      have hXeq : (X ^ ((1:ℝ)/2)) ^ (2:ℝ) = X := by
        rw [← Real.rpow_mul hXnonneg, show (1:ℝ)/2*2 = 1 by norm_num, Real.rpow_one]
      have hRHSeq : ((2 + Pival) ^ Cglob) ^ (2:ℝ) = (2 + Pival) ^ (2 * Cglob) := by
        rw [← Real.rpow_mul hPpos.le]
        congr 1
        ring
      rw [hXeq, hRHSeq] at hstep1
      exact hstep1
    have hPivalle : Pival ≤ (2 + Pival) ^ (1:ℝ) := by
      rw [Real.rpow_one]; linarith only []
    have h3le2 : (3:ℝ) ^ (-((3:ℝ)/2 * ((s:ℝ) - (jStar:ℝ)))) ≤ (2 + Pival) ^ (-((3:ℝ)/2 * B)) :=
      hdecay2
    have step_a2 : Pival * X ≤ (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) :=
      mul_le_mul hPivalle hXsq hXnonneg (Real.rpow_nonneg hPpos.le 1)
    have step_b2 : Pival * X * (3:ℝ) ^ (-((3:ℝ)/2 * ((s:ℝ) - (jStar:ℝ)))) ≤
        (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-((3:ℝ)/2 * B)) :=
      mul_le_mul step_a2 h3le2 (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)
        (mul_nonneg (Real.rpow_nonneg hPpos.le 1) (Real.rpow_nonneg hPpos.le (2 * Cglob)))
    have hcomb2 : (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-((3:ℝ)/2 * B))
        = (2 + Pival) ^ (1 + 2 * Cglob - (3:ℝ)/2 * B) := by
      rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
      congr 1
    calc
      (1:ℝ) * Pival * X * (3:ℝ) ^ (-((3:ℝ)/2 * ((s:ℝ) - (jStar:ℝ))))
          = Pival * X * (3:ℝ) ^ (-((3:ℝ)/2 * ((s:ℝ) - (jStar:ℝ)))) := by rw [one_mul]
      _ ≤ (2 + Pival) ^ (1:ℝ) * (2 + Pival) ^ (2 * Cglob) * (2 + Pival) ^ (-((3:ℝ)/2 * B)) :=
          step_b2
      _ = (2 + Pival) ^ (1 + 2 * Cglob - (3:ℝ)/2 * B) := hcomb2
      _ ≤ 1 := hchain2

/-- `G = ((Id,0),(g,Id))` acts as `(x1, x2) => (x1, g x1 + x2)`. -/
private theorem blockMatVecMul_respG (F : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (respG F) X = (X.1, matVecMul (respg F) X.1 + X.2) := by
  have h1 : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := by
    intro x; funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have h0 : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x; funext i; simp [matVecMul]
  simp [blockMatVecMul, respG, h1, h0]

private theorem matVecMul_sub (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  funext i
  simp [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem matVecMul_neg (A : Mat d) (x : Vec d) :
    matVecMul A (-x) = -(matVecMul A x) := by
  funext i
  simp [matVecMul, mul_neg, Finset.sum_neg_distrib]

/-- A skew matrix has vanishing quadratic form. -/
theorem vecDot_skew_self_of_matTranspose (h : Mat d) (hh : matTranspose h = -h) (x : Vec d) :
    vecDot x (matVecMul h x) = 0 := by
  have hv : vecDot x (matVecMul h x) = x ⬝ᵥ h *ᵥ x := rfl
  have key : x ⬝ᵥ h *ᵥ x = -(x ⬝ᵥ h *ᵥ x) := by
    calc x ⬝ᵥ h *ᵥ x = x ᵥ* h ⬝ᵥ x := by rw [Matrix.dotProduct_mulVec]
      _ = hᵀ *ᵥ x ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = (-h) *ᵥ x ⬝ᵥ x := by rw [show (hᵀ : Mat d) = -h from hh]
      _ = -(h *ᵥ x ⬝ᵥ x) := by rw [Matrix.neg_mulVec, neg_dotProduct]
      _ = -(x ⬝ᵥ h *ᵥ x) := by rw [dotProduct_comm]
  rw [hv]; linarith only [key]

/-- The reciprocal normalizations: `p. q = e. e`. -/
private theorem vecDot_respP_respQ_eq_vecDot_self {A : BlockMat d} (hM : (respM A).PosDef) (e : Vec d) :
    vecDot (respP A e) (respQ A e) = vecDot e e := by
  have hherm : (matSqrt (respM A))ᵀ = matSqrt (respM A) := by
    have h := HCPolySupport.HighContrast.conjTranspose_matSqrt hM.posSemidef
    rwa [HCPolySupport.HighContrast.conjTranspose_eq_transpose'] at h
  have hcancel : matSqrt (respM A) * matSqrt (respM A)⁻¹ = 1 := (GeometricMean.sqrtCancel hM).1
  calc vecDot (respP A e) (respQ A e)
      = matSqrt (respM A)⁻¹ *ᵥ e ⬝ᵥ matSqrt (respM A) *ᵥ e := rfl
    _ = (matSqrt (respM A)⁻¹ *ᵥ e) ᵥ* matSqrt (respM A) ⬝ᵥ e := by
        rw [Matrix.dotProduct_mulVec]
    _ = (matSqrt (respM A))ᵀ *ᵥ (matSqrt (respM A)⁻¹ *ᵥ e) ⬝ᵥ e := by
        rw [Matrix.mulVec_transpose]
    _ = (matSqrt (respM A) * matSqrt (respM A)⁻¹) *ᵥ e ⬝ᵥ e := by
        rw [hherm, Matrix.mulVec_mulVec]
    _ = vecDot e e := by rw [hcancel, Matrix.one_mulVec]; rfl

/-- `respSkew` is skew. -/
private theorem respSkew_isSkew_matTranspose (A : BlockMat d) :
    matTranspose (respSkew A) = -(respSkew A) := by
  simp only [respSkew, matTranspose, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose]
  module

/-- `G x^- = (-p, q - h_t p)`: the recentring cancels `g` in the second slot. -/
private theorem respG_respxMinus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    blockMatVecMul (respG F) (respxMinus P jStar F t e)
      = (-(respP (respMean P jStar F t) e),
          respQ (respMean P jStar F t) e
            - matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e)) := by
  rw [blockMatVecMul_respG]
  simp only [respxMinus, respqMinus, matVecMul_sub, matVecMul_neg, Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

/-- `(L^-)^2 = (-p, q - h_t p). E_t (-p, q - h_t p)`. -/
theorem respLsqMinus_eq (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqMinus P jStar F t e
      = blockVecDot
          (-(respP (respMean P jStar F t) e),
            respQ (respMean P jStar F t) e
              - matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e))
          (blockMatVecMul (respMean P jStar F t)
            (-(respP (respMean P jStar F t) e),
              respQ (respMean P jStar F t) e
                - matVecMul (respSkew (respMean P jStar F t))
                  (respP (respMean P jStar F t) e))) := by
  rw [respLsqMinus_eq_quadratic, respEhatMinus, blockVecDot_blockCongr, respG_respxMinus]

/-- `D = diag(Id,-Id)` acts as `(x1,x2) => (x1,-x2)`. -/
private theorem blockMatVecMul_blockD (X : BlockVec d) :
    blockMatVecMul (blockD d) X = (X.1, -X.2) := by
  have h1 : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := by
    intro x; funext i; simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have h0 : ∀ x : Vec d, matVecMul (0 : Mat d) x = 0 := by
    intro x; funext i; simp [matVecMul]
  have hn : ∀ x : Vec d, matVecMul (-1 : Mat d) x = -x := by
    intro x; funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  simp [blockMatVecMul, blockD, h1, h0, hn]

/-- `(L^+)^2 = (-p, -(q + h_t p)). E_t (-p, -(q + h_t p))`. -/
theorem respLsqPlus_eq (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) :
    respLsqPlus P jStar F t e
      = blockVecDot
          (-(respP (respMean P jStar F t) e),
            -(respQ (respMean P jStar F t) e
              + matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e)))
          (blockMatVecMul (respMean P jStar F t)
            (-(respP (respMean P jStar F t) e),
              -(respQ (respMean P jStar F t) e
                + matVecMul (respSkew (respMean P jStar F t))
                  (respP (respMean P jStar F t) e)))) := by
  have hfst : (blockMatVecMul (respG F)
        (blockMatVecMul (blockD d) (respxPlus P jStar F t e))).1
      = -(respP (respMean P jStar F t) e) := by
    rw [blockMatVecMul_blockD, blockMatVecMul_respG]
    rfl
  have hsnd : (blockMatVecMul (respG F)
        (blockMatVecMul (blockD d) (respxPlus P jStar F t e))).2
      = -(respQ (respMean P jStar F t) e
          + matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e)) := by
    rw [blockMatVecMul_blockD, blockMatVecMul_respG]
    simp only [respxPlus, respqPlus, matVecMul_sub, matVecMul_neg]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  have hv : blockMatVecMul (respG F) (blockMatVecMul (blockD d) (respxPlus P jStar F t e))
      = (-(respP (respMean P jStar F t) e),
          -(respQ (respMean P jStar F t) e
            + matVecMul (respSkew (respMean P jStar F t)) (respP (respMean P jStar F t) e))) :=
    Prod.ext_iff.mpr ⟨hfst, hsnd⟩
  rw [respLsqPlus_eq_quadratic, respEhatPlus, blockAdjoint, blockVecDot_blockCongr, respEhatMinus,
    blockVecDot_blockCongr, hv]

/-- Entries of `annealedBlockOf` are the expectations of the pathwise entries. -/
private theorem blockMatEntry_annealedBlockOf (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (α β : BlockCoord d) :
    blockMatEntry (annealedBlockOf P V b) α β
      = ∫ a, blockMatEntry (coarseBlockMatrix V (b a)) α β ∂P := by
  cases α <;> cases β <;> rfl

/-- The quadratic form of a doubled block, entrywise. -/
private theorem blockVecDot_entries (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X)
      = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α * blockMatEntry A α β * toFullBlockVec X β := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, toFullBlockMat_eq_blockMatEntry]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- The annealed quadratic form is the expectation of the pathwise quadratic form. -/
private theorem integral_blockVecDot (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (X : BlockVec d)
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P) :
    (∫ a, blockVecDot X (blockMatVecMul (coarseBlockMatrix V (b a)) X) ∂P)
      = blockVecDot X (blockMatVecMul (annealedBlockOf P V b) X) := by
  simp only [blockVecDot_entries, blockMatEntry_annealedBlockOf]
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ =>
    (((hint α β).const_mul (toFullBlockVec X α)).mul_const (toFullBlockVec X β))))]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ (fun β _ =>
    (((hint α β).const_mul (toFullBlockVec X α)).mul_const (toFullBlockVec X β)))]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_mul_const, integral_const_mul]

private theorem vecDot_add_right_distrib (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

/-- The reciprocal normalizations: `p. q^- = 1` (the skew part cancels). -/
theorem vecDot_respP_respqMinus_eq_one (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F)) :
    vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) = 1 := by
  have h2 := respSkew_isSkew_matTranspose (respMean P jStar F t)
  have hskew : matTranspose (respg F - respSkew (respMean P jStar F t))
      = -(respg F - respSkew (respMean P jStar F t)) := by
    simp only [matTranspose, Matrix.transpose_sub] at hg h2 ⊢
    rw [hg, h2]; abel
  rw [respqMinus, vecDot_add_right_distrib, vecDot_respP_respQ_eq_vecDot_self hM, he,
    vecDot_skew_self_of_matTranspose _ hskew, add_zero]

/-- The reciprocal normalizations: `p. q^+ = 1`. -/
theorem vecDot_respP_respqPlus_eq_one (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F)) :
    vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) = 1 := by
  have h2 := respSkew_isSkew_matTranspose (respMean P jStar F t)
  have hskew : matTranspose (respSkew (respMean P jStar F t) - respg F)
      = -(respSkew (respMean P jStar F t) - respg F) := by
    simp only [matTranspose, Matrix.transpose_sub] at hg h2 ⊢
    rw [hg, h2]; abel
  rw [respqPlus, vecDot_add_right_distrib, vecDot_respP_respQ_eq_vecDot_self hM, he,
    vecDot_skew_self_of_matTranspose _ hskew, add_zero]

/-- Congruence is monotone for the Loewner order. -/
theorem blockCongr_mono (G : BlockMat d) {A B : BlockMat d}
    (h : BlockMatLoewnerLE A B) : BlockMatLoewnerLE (blockCongr G A) (blockCongr G B) := by
  intro X
  rw [blockVecDot_blockCongr, blockVecDot_blockCongr]
  exact h _

/-- Integrability of the pathwise quadratic form from entrywise integrability. -/
private theorem integrable_blockVecDot (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (b : CoeffSpace d → CoeffField d) (X : BlockVec d)
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (coarseBlockMatrix V (b a)) X)) P := by
  simp only [blockVecDot_entries]
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    ((hint α β).const_mul _).mul_const _

/-- The third conjunct of the response energy and defect estimate, conditional on the three bridge
inputs `hpath`, `hint`, `hann`
(`p.response.transfer`). -/
theorem respEJMinus_eq (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F))
    (hpath : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (respxMinus P jStar F t e)
            (blockMatVecMul (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
              (respxMinus P jStar F t e))
          - vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e))
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry
        (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a)) α β) P)
    (hann : annealedBlockOf P (respCell jStar F t) (respCoeffMinus F)
        = respEhatMinus P jStar F t) :
    respEJMinus P jStar F t e = (1 / 2 : ℝ) * respLsqMinus P jStar F t e - 1 := by
  have hpq := vecDot_respP_respqMinus_eq_one P jStar F t e he hM hg
  have hQint := integrable_blockVecDot P (respCell jStar F t) (respCoeffMinus F)
    (respxMinus P jStar F t e) hint
  have hQ := integral_blockVecDot P (respCell jStar F t) (respCoeffMinus F)
    (respxMinus P jStar F t e) hint
  have huniv : P.real Set.univ = 1 := by simp
  rw [respEJMinus]
  simp only [hpath, hpq]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv]
  simp [respLsqMinus_eq_quadratic]

/-- The fourth conjunct of the response energy and defect estimate, conditional on the three
bridge inputs. -/
theorem respEJPlus_eq (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) (he : vecDot e e = 1)
    (hM : (respM (respMean P jStar F t)).PosDef)
    (hg : matTranspose (respg F) = -(respg F))
    (hpath : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) t (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (respxPlus P jStar F t e)
            (blockMatVecMul (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
              (respxPlus P jStar F t e))
          - vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e))
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry
        (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a)) α β) P)
    (hann : annealedBlockOf P (respCell jStar F t) (respCoeffPlus F)
        = respEhatPlus P jStar F t) :
    respEJPlus P jStar F t e = (1 / 2 : ℝ) * respLsqPlus P jStar F t e - 1 := by
  have hpq := vecDot_respP_respqPlus_eq_one P jStar F t e he hM hg
  have hQint := integrable_blockVecDot P (respCell jStar F t) (respCoeffPlus F)
    (respxPlus P jStar F t e) hint
  have hQ := integral_blockVecDot P (respCell jStar F t) (respCoeffPlus F)
    (respxPlus P jStar F t e) hint
  have huniv : P.real Set.univ = 1 := by simp
  rw [respEJPlus]
  simp only [hpath, hpq]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv]
  simp [respLsqPlus_eq_quadratic]

/-- The annealed response at one adapted cell, from the pathwise identity, entrywise
integrability, and the annealed-block identification. -/
theorem integral_respJ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (qq : Mat d) (u : ℤ) (p r : Vec d) (b : CoeffSpace d → CoeffField d) (X : BlockVec d)
    (Aann : BlockMat d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p r (b a)
      = (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) X)
        - vecDot p r)
    (hint : ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β) P)
    (hann : annealedBlockOf P (HighContrast.adaptedCell qq u) b = Aann) :
    (∫ a, respJ qq u p r (b a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul Aann X) - vecDot p r := by
  have huniv : P.real Set.univ = 1 := by simp
  have hQint := integrable_blockVecDot P (HighContrast.adaptedCell qq u) b X hint
  have hQ := integral_blockVecDot P (HighContrast.adaptedCell qq u) b X hint
  simp only [hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv]
  simp

/-- The defect at the minus load, conditional on the bridge inputs at both scales
(`e.response.energy.and.defect`, `p.response.transfer`). -/
theorem respTauMinus_eq (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (hpath_s : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (respxMinus P jStar F t e)
            (blockMatVecMul (coarseBlockMatrix (respCell jStar F s) (respCoeffMinus F a))
              (respxMinus P jStar F t e))
          - vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e))
    (hint_s : ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (respCell jStar F s) (respCoeffMinus F a)) α β) P)
    (hann_s : annealedBlockOf P (respCell jStar F s) (respCoeffMinus F)
        = respEhatMinus P jStar F s)
    (hEJ : respEJMinus P jStar F t e = (1 / 2 : ℝ) * respLsqMinus P jStar F t e - 1)
    (hpq : vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) = 1) :
    respTauMinus P jStar F s t e
      = (1 / 2 : ℝ) * blockVecDot (respxMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F s) (respxMinus P jStar F t e))
        - (1 / 2 : ℝ) * respLsqMinus P jStar F t e := by
  have hs := integral_respJ P (respGrid jStar F) s (respP (respMean P jStar F t) e)
    (respqMinus P jStar F t e) (respCoeffMinus F) (respxMinus P jStar F t e)
    (respEhatMinus P jStar F s) hpath_s hint_s hann_s
  rw [respTauMinus, hs, hEJ, hpq]
  ring

/-- The defect is nonnegative once `Ehat_t <= Ehat_s` (`Annealed.adaptedMean_antitone`). -/
theorem zero_le_respTauMinus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (hLoew : BlockMatLoewnerLE (respEhatMinus P jStar F t) (respEhatMinus P jStar F s))
    (hτ : respTauMinus P jStar F s t e
      = (1 / 2 : ℝ) * blockVecDot (respxMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F s) (respxMinus P jStar F t e))
        - (1 / 2 : ℝ) * respLsqMinus P jStar F t e) :
    0 ≤ respTauMinus P jStar F s t e := by
  have h := hLoew (respxMinus P jStar F t e)
  rw [hτ, respLsqMinus_eq_quadratic]
  linarith only [h]

/-- The congruence `Ehat^- = G^t E G` is Loewner-monotone in `E`. -/
theorem respEhatMinus_mono (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (h : BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s)) :
    BlockMatLoewnerLE (respEhatMinus P jStar F t) (respEhatMinus P jStar F s) :=
  blockCongr_mono _ h

end HCPolySupport.HighContrast.Multiscale
end
