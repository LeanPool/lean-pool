/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorDiscrete
public import LeanPool.HighContrastHomogenization.Provider.Window.Successor
public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedPolynomialNormalizer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGaussianGauge

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangePoweredGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The powered finite-range gauge

The window mechanism reads the tail of a coarse-ellipticity datum against the
`μ`-powered Gaussian `exp(c t^(2μ))`, `μ = d/2 - g`, rather than against the
Gaussian itself.  This file records the corresponding powered form of the
finite-range gauge supplied by unit range of dependence,

`Ψ_fr^{(μ)}(t) = exp(c_fr(d) t^(2μ))`,

together with the two properties a gauge must have before it can appear in a
coarse-ellipticity datum: admissibility and the growth inequality, the latter at
a growth witness depending on the dimension and on `μ` alone.  Reading the
stopping-radius provider against this gauge makes its domination premise an
identity, so the shifted tail the bad-tail engine consumes holds with the
dimensional constant `c_fr(d)`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

/-! ## The gauge and its witness -/

/-- The `μ`-powered finite-range gauge `Ψ_fr^{(μ)}(t) = exp(c_fr(d) t^(2μ))`. -/
@[expose]
def frPoweredGauge (d : ℕ) (mu : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (frGaugeConst d * t ^ (2 * mu))

/-- A growth witness for the powered finite-range gauge, depending on the
dimension and on `μ` alone. -/
@[expose]
def frPoweredGrowthWitness (d : ℕ) (mu : ℝ) : ℝ :=
  3 + (1 + (2 * mu * frGaugeConst d)⁻¹) ^ (2 * mu)⁻¹

/-! ## Admissibility -/

theorem admissiblePsi_frPoweredGauge (d : ℕ) {mu : ℝ} (hmu : 0 < mu) :
    IndependentSums.AdmissiblePsi (frPoweredGauge d mu) := by
  have h2mu : (0 : ℝ) ≤ 2 * mu := by linarith only [hmu]
  constructor
  · intro s hs t _ hst
    simp only [Set.mem_Ici] at hs
    refine Real.exp_le_exp.2 ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hst h2mu)
      (frGaugeConst_pos d).le
  · intro t ht
    have h0 : (0 : ℝ) ≤ frGaugeConst d * t ^ (2 * mu) :=
      mul_nonneg (frGaugeConst_pos d).le (Real.rpow_nonneg ht _)
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (frGaugeConst d * t ^ (2 * mu)) := Real.exp_le_exp.2 h0

theorem three_le_frPoweredGrowthWitness (d : ℕ) {mu : ℝ} (hmu : 0 < mu) :
    (3 : ℝ) ≤ frPoweredGrowthWitness d mu := by
  have h2mu : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have hApos : (0 : ℝ) < 1 + (2 * mu * frGaugeConst d)⁻¹ := by
    have hc := frGaugeConst_pos d
    have hprod : (0 : ℝ) < 2 * mu * frGaugeConst d := by positivity
    have hinv : (0 : ℝ) < (2 * mu * frGaugeConst d)⁻¹ := inv_pos.2 hprod
    linarith only [hinv]
  have hpow : (0 : ℝ) ≤ (1 + (2 * mu * frGaugeConst d)⁻¹) ^ (2 * mu)⁻¹ :=
    Real.rpow_nonneg hApos.le _
  rw [frPoweredGrowthWitness]
  linarith only [hpow]

/-! ## The growth inequality -/

/-- The growth witness dominates the reciprocal of the gauge constant after
raising to the power `2μ`.  This is the only property of the witness the growth
inequality uses. -/
theorem le_frPoweredGrowthWitness_rpow (d : ℕ) {mu : ℝ} (hmu : 0 < mu) :
    1 + (2 * mu * frGaugeConst d)⁻¹ ≤ frPoweredGrowthWitness d mu ^ (2 * mu) := by
  have h2mu : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have hc := frGaugeConst_pos d
  have hprod : (0 : ℝ) < 2 * mu * frGaugeConst d := by positivity
  have hApos : (0 : ℝ) < 1 + (2 * mu * frGaugeConst d)⁻¹ := by
    have hinv : (0 : ℝ) < (2 * mu * frGaugeConst d)⁻¹ := inv_pos.2 hprod
    linarith only [hinv]
  have hroot : (1 + (2 * mu * frGaugeConst d)⁻¹) ^ (2 * mu)⁻¹ ≤
      frPoweredGrowthWitness d mu := by
    rw [frPoweredGrowthWitness]
    linarith only []
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hApos.le _) hroot h2mu.le
  rwa [← Real.rpow_mul hApos.le, inv_mul_cancel₀ (ne_of_gt h2mu), Real.rpow_one] at hmono

theorem hasPsiGrowth_frPoweredGauge (d : ℕ) {mu : ℝ} (hmu : 0 < mu) :
    IndependentSums.HasPsiGrowth (frPoweredGauge d mu) (frPoweredGrowthWitness d mu) := by
  intro t ht
  have h2mu : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hc : 0 < frGaugeConst d := frGaugeConst_pos d
  have hKnonneg : (0 : ℝ) ≤ frPoweredGrowthWitness d mu :=
    le_trans (by norm_num) (three_le_frPoweredGrowthWitness d hmu)
  have hprodrw : (frPoweredGrowthWitness d mu * t) ^ (2 * mu)
      = frPoweredGrowthWitness d mu ^ (2 * mu) * t ^ (2 * mu) :=
    Real.mul_rpow hKnonneg htpos.le
  have hT1 : (1 : ℝ) ≤ t ^ (2 * mu) := by
    have h := Real.rpow_le_rpow zero_le_one ht h2mu.le
    rwa [Real.one_rpow] at h
  have hlogeq : Real.log (t ^ (2 * mu)) = 2 * mu * Real.log t := Real.log_rpow htpos _
  have hlogle : Real.log (t ^ (2 * mu)) ≤ t ^ (2 * mu) - 1 :=
    Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hT1)
  have hwitness := le_frPoweredGrowthWitness_rpow d hmu
  set L : ℝ := Real.log t with hLdef
  set T : ℝ := t ^ (2 * mu) with hTdef
  set Kp : ℝ := frPoweredGrowthWitness d mu ^ (2 * mu) with hKpdef
  clear_value L T Kp
  have hlogbound : 2 * mu * L ≤ T - 1 := by
    rw [hlogeq] at hlogle
    exact hlogle
  have hgap : (2 * mu)⁻¹ ≤ frGaugeConst d * (Kp - 1) := by
    have hstep : frGaugeConst d * (2 * mu * frGaugeConst d)⁻¹ ≤ frGaugeConst d * (Kp - 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hwitness]) hc.le
    have hid : frGaugeConst d * (2 * mu * frGaugeConst d)⁻¹ = (2 * mu)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_comm (frGaugeConst d) ((2 * mu)⁻¹), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hc), mul_one]
    rw [hid] at hstep
    exact hstep
  have hmulT : (2 * mu)⁻¹ * T ≤ frGaugeConst d * (Kp - 1) * T := by
    have hTpos : (0 : ℝ) ≤ T := by linarith only [hT1]
    exact mul_le_mul_of_nonneg_right hgap hTpos
  have hLbound : L ≤ (2 * mu)⁻¹ * T := by
    have hinvpos : (0 : ℝ) < (2 * mu)⁻¹ := inv_pos.2 h2mu
    have hscale := mul_le_mul_of_nonneg_left hlogbound hinvpos.le
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h2mu), one_mul] at hscale
    nlinarith only [hscale, hinvpos, hT1]
  have harg : L + frGaugeConst d * T ≤ frGaugeConst d * (Kp * T) := by
    nlinarith only [hLbound, hmulT]
  have hrw : t * frPoweredGauge d mu t = Real.exp (L + frGaugeConst d * T) := by
    rw [Real.exp_add, hLdef, Real.exp_log htpos, frPoweredGauge, hTdef]
  rw [hrw, frPoweredGauge, hprodrw]
  exact Real.exp_le_exp.2 harg

/-! ## The domination premise is an identity -/

end

end Quenched
end HighContrast
end HCPolySupport
