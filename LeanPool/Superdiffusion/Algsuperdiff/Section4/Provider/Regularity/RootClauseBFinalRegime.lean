/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFinalArith

/-!
# RootClauseBFinalRegime

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The bundle -/

/-- **Every `γ`-regime clause the clause-(B) chain consumes**, at one model.

`C` is the Step-6 producer's regime constant, `C_ann` its annular companion,
`C_ind` the all-scales induction-state constant, `C₁` the Step-1 constant the
display is stated at, and `C_rg` the constant of the printed `α`-range. -/
structure RootClauseBGammaFacts (M : ABKModel d) (C Cann Cind C1 Crg : ℝ) : Prop where
  /-- `γ < 1/2`: the standing Step-5 ratio gate. -/
  ltHalf : M.gamma < 1 / 2
  /-- `γ ≤ 1/4`: the `M`-uniform funding enlargement's gate. -/
  leQuarter : M.gamma ≤ 1 / 4
  /-- `γ ≤ 1/256`: the Step-6 producer's own numeral. -/
  le256 : M.gamma ≤ 1 / 256
  /-- The Step-6 producer's first regime clause. -/
  regimeC : M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ)
  /-- The Step-6 producer's annular regime clause. -/
  regimeAnn : M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ)
  /-- The induction-state regime clause. -/
  regimeInd : M.gamma ≤ (Cind⁻¹) ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ)
  /-- The Step-1 floor `8γ ≤ s/8` of the `A6` cap producer. -/
  floorEight : 8 * M.gamma ≤ stepOneSEighth
  /-- The `α`-free `γ|log γ|²` gate of the Step-6 producer. -/
  smallFree : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
    Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
      (C⁻¹ * stepOneS ^ (4 : ℕ))
  /-- The `α`-dependent `γ|log γ|²` gate, at every `α` in the printed range. -/
  smallEp : ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - Crg * Real.sqrt M.gamma →
    M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
        stepOneEp (stepOneDelta C1 alpha)

/-! ## 2. The two scalar thresholds -/

/-- The right-hand side of the `α`-free gate, as a positive constant. -/
def rootClauseBGateFree (cstar C : ℝ) : ℝ :=
  Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * cstar ^ (2 : ℕ) * (C⁻¹ * stepOneS ^ (4 : ℕ))

/-- The `γ^{1/4}`-coefficient of the `α`-dependent gate, as a positive constant. -/
def rootClauseBGateEp (cstar C1 Crg : ℝ) : ℝ :=
  Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) *
    (stepOneSEighth * Real.sqrt (C1⁻¹ * Crg))

theorem rootClauseBGateFree_pos {cstar C : ℝ} (hcstar : 0 < cstar) (hC : 0 < C) :
    0 < rootClauseBGateFree cstar C := by
  have h1 : (0 : ℝ) < Real.rpow (stepOneS / 8) (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by rw [stepOneS]; norm_num) _
  have h2 : (0 : ℝ) < cstar ^ (2 : ℕ) := pow_pos hcstar 2
  have h3 : (0 : ℝ) < C⁻¹ * stepOneS ^ (4 : ℕ) :=
    mul_pos (inv_pos.mpr hC) (pow_pos (by rw [stepOneS]; norm_num) 4)
  rw [rootClauseBGateFree]
  exact mul_pos (mul_pos h1 h2) h3

theorem rootClauseBGateEp_pos {cstar C1 Crg : ℝ} (hcstar : 0 < cstar) (hC1 : 0 < C1)
    (hCrg : 0 < Crg) : 0 < rootClauseBGateEp cstar C1 Crg := by
  have h1 : (0 : ℝ) < Real.rpow stepOneSEighth (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos stepOneSEighth_pos _
  have h2 : (0 : ℝ) < cstar ^ (2 : ℕ) := pow_pos hcstar 2
  have h3 : (0 : ℝ) < Real.sqrt (C1⁻¹ * Crg) :=
    Real.sqrt_pos.mpr (mul_pos (inv_pos.mpr hC1) hCrg)
  rw [rootClauseBGateEp]
  exact mul_pos (mul_pos h1 h2) (mul_pos stepOneSEighth_pos h3)

/-- **The Step-1 amplitude at the printed `α`-range**: `ε(δ) ≥
(s/8)√(C₁⁻¹C)γ^{1/4}`. -/
theorem stepOneEp_ge_rpow_quarter {C1 Crg g alpha : ℝ} (hC1 : 0 < C1) (hCrg : 0 < Crg)
    (hg : 0 < g) (halpha : alpha ≤ 1 - Crg * Real.sqrt g) :
    stepOneSEighth * Real.sqrt (C1⁻¹ * Crg) * g ^ (1 / 4 : ℝ) ≤
      stepOneEp (stepOneDelta C1 alpha) := by
  have hinv : (0 : ℝ) ≤ C1⁻¹ := (inv_pos.mpr hC1).le
  have hsub : Crg * Real.sqrt g ≤ 1 - alpha := by linarith only [halpha]
  have hdelta : C1⁻¹ * (Crg * Real.sqrt g) ≤ stepOneDelta C1 alpha := by
    rw [stepOneDelta]
    exact mul_le_mul_of_nonneg_left hsub hinv
  have hsqrtmono : Real.sqrt (C1⁻¹ * (Crg * Real.sqrt g)) ≤
      Real.sqrt (stepOneDelta C1 alpha) := Real.sqrt_le_sqrt hdelta
  have hfac : Real.sqrt (C1⁻¹ * (Crg * Real.sqrt g)) =
      Real.sqrt (C1⁻¹ * Crg) * g ^ (1 / 4 : ℝ) := by
    have hassoc : C1⁻¹ * (Crg * Real.sqrt g) = (C1⁻¹ * Crg) * Real.sqrt g := by ring
    have hquarter : Real.sqrt (Real.sqrt g) = g ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hg.le]
      norm_num
    rw [hassoc, Real.sqrt_mul (mul_nonneg hinv hCrg.le), hquarter]
  rw [stepOneEp, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ stepOneSEighth_pos.le
  rw [← hfac]
  exact hsqrtmono

/-! ## 3. The producer -/

/-- **One `γ₀` for the whole clause-(B) chain.**

The threshold is the minimum of the printed numeral `1/256`, the three
`c⋆¹⁰`-regimes, and the two `γ|log γ|²` thresholds of `RootClauseBFinalArith`
§4.  Every clause of `RootClauseBGammaFacts` then holds for every model in the
regime, and the `α`-dependent one holds at every `α` of the printed range. -/
theorem exists_rootClauseBGammaFacts (d : ℕ) {cstar C Cann Cind C1 Crg : ℝ}
    (hcstar : 0 < cstar) (hC : 0 < C) (hCann : 0 < Cann) (hCind : 0 < Cind)
    (hC1 : 0 < C1) (hCrg : 0 < Crg) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        RootClauseBGammaFacts M C Cann Cind C1 Crg := by
  set A : ℝ := rootClauseBGateFree cstar C with hAdef
  set B : ℝ := rootClauseBGateEp cstar C1 Crg with hBdef
  have hApos : 0 < A := by rw [hAdef]; exact rootClauseBGateFree_pos hcstar hC
  have hBpos : 0 < B := by rw [hBdef]; exact rootClauseBGateEp_pos hcstar hC1 hCrg
  have hcs10 : (0 : ℝ) < cstar ^ (10 : ℕ) := pow_pos hcstar 10
  refine ⟨min (1 / 256)
      (min (min (C⁻¹ * cstar ^ (10 : ℕ)) (Cann⁻¹ * cstar ^ (10 : ℕ)))
        (min ((Cind⁻¹) ^ (10 : ℕ) * cstar ^ (10 : ℕ))
          (min ((A / 64) ^ (4 / 3 : ℝ)) ((B / 64) ^ (2 : ℕ))))), ?_, ?_⟩
  · refine lt_min (by norm_num) (lt_min (lt_min ?_ ?_) (lt_min ?_ (lt_min ?_ ?_)))
    · exact mul_pos (inv_pos.mpr hC) hcs10
    · exact mul_pos (inv_pos.mpr hCann) hcs10
    · exact mul_pos (pow_pos (inv_pos.mpr hCind) 10) hcs10
    · exact Real.rpow_pos_of_pos (by linarith only [hApos]) _
    · exact pow_pos (by linarith only [hBpos]) 2
  intro M hcs hgamma
  have hg0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have h256 : M.gamma ≤ 1 / 256 := le_trans hgamma (min_le_left _ _)
  have hrest := le_trans hgamma (min_le_right _ _)
  have hpair := le_trans hrest (min_le_left _ _)
  have hrest2 := le_trans hrest (min_le_right _ _)
  have hind := le_trans hrest2 (min_le_left _ _)
  have hgates := le_trans hrest2 (min_le_right _ _)
  have hgA := le_trans hgates (min_le_left _ _)
  have hgB := le_trans hgates (min_le_right _ _)
  have hg1 : M.gamma ≤ 1 := by linarith only [h256]
  refine
    { ltHalf := by linarith only [h256]
      leQuarter := by linarith only [h256]
      le256 := h256
      regimeC := by rw [hcs]; exact le_trans hpair (min_le_left _ _)
      regimeAnn := by rw [hcs]; exact le_trans hpair (min_le_right _ _)
      regimeInd := by rw [hcs]; exact hind
      floorEight := by
        rw [stepOneSEighth, stepOneS]
        linarith only [h256]
      smallFree := by
        rw [hcs]
        exact gamma_log_sq_le_of_le_threshold hg0 hg1 hApos hgA
      smallEp := ?_ }
  intro alpha halpha0 halpha
  rw [hcs]
  refine le_trans (gamma_log_sq_le_rpow_quarter hg0 hg1 hBpos hgB) ?_
  have hstep := stepOneEp_ge_rpow_quarter hC1 hCrg hg0 halpha
  have hcoef : (0 : ℝ) ≤ Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) :=
    mul_nonneg (Real.rpow_pos_of_pos stepOneSEighth_pos _).le (pow_nonneg hcstar.le 2)
  have hexpand : B * M.gamma ^ (1 / 4 : ℝ) =
      Real.rpow stepOneSEighth (3 / 2 : ℝ) * cstar ^ (2 : ℕ) *
        (stepOneSEighth * Real.sqrt (C1⁻¹ * Crg) * M.gamma ^ (1 / 4 : ℝ)) := by
    rw [hBdef, rootClauseBGateEp]
    ring
  rw [hexpand]
  exact mul_le_mul_of_nonneg_left hstep hcoef

end

end Algsuperdiff.Section4.Provider.Regularity
