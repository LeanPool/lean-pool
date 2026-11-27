/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.InfiniteRenyiInterpolation
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteSemidefiniteRenyiInterpolation
public import LeanPool.VacuumBellSeparation.Gaussian.RenyiTwoTraceDistance

/-!
# General positive-input interpolation and trace-distance consequence

Finite positive-reference mixtures remove the input-injectivity premise
before the actual spectral compression limit. Thus every positive trace-one
input and faithful reference satisfy the full Hilbert-space interpolation
and trace-distance inequalities, including infinite Renyi quantity. No
Gaussian structure or bounded inverse of the reference is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Matrix
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem finite_spectral_semidefinite_sandwich_square_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : HilbertBasis ι ℂ E)
    (f : κ → ι) (hfinj : Function.Injective f) {ρ σ Θ Ξ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1) (hσ : IsFaithfulDensity σ)
    {a : ι → ℝ} (ha : ∀ j, σ (b j) = a j • b j) {r : ℝ} (hr : 2 ≤ r)
    (hΘ : 0 ≤ Θ) (hcΘ : IsCompactOperator Θ)
    (hfΘ : σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ)
    (hfΞ : σ ^ ((1 / 2 : ℝ) / 2) * Ξ * σ ^ ((1 / 2 : ℝ) / 2) = ρ) :
    finitePositivePowerTrace (finiteBasisCompression b f hfinj Ξ) 2 ≤
      positiveTrace (Θ ^ r) ^ (1 / (r - 1)) := by
  have hr₁ : 1 < r := by linarith
  have hexp : 0 ≤ 1 / (r - 1) := (one_div_pos.mpr (sub_pos.mpr hr₁)).le
  let R := finiteBasisCompression b f hfinj ρ
  let S := finiteBasisCompression b f hfinj σ
  have hR : R.PosSemidef := finiteBasisCompression_posSemidef b f hfinj hρ
  have hS : S.PosDef := finiteBasisCompression_posDef b f hfinj hσ.1 hσ.2.2
  have hRt : R.trace.re ≤ 1 := by
    apply ENNReal.ofReal_le_one.mp
    have h := finiteBasisCompression_trace_le b f hfinj hρ
    simpa only [hρt] using h
  have hSt : S.trace.re ≤ 1 := by
    apply ENNReal.ofReal_le_one.mp
    have h := finiteBasisCompression_trace_le b f hfinj hσ.1
    simpa only [hσ.2.1] using h
  have hfinite := finite_semidefinite_sandwichedRenyi_interpolation hR hS hRt hSt hr
  have hbase : 0 ≤ ((finiteRenyiSandwich R S (gaussianRenyiTau r)) ^ r).trace.re :=
    (Complex.nonneg_iff.mp
      ((CFC.rpow_nonneg (a := finiteRenyiSandwich R S (gaussianRenyiTau r))
        (y := r)).posSemidef.trace_nonneg)).1
  have hbound := ENNReal.ofReal_le_ofReal hfinite
  change finitePositivePowerTrace (finiteRenyiSandwich R S (1 / 2)) 2 ≤
    ENNReal.ofReal (((finiteRenyiSandwich R S (gaussianRenyiTau r)) ^ r).trace.re ^
      (1 / (r - 1))) at hbound
  rw [← ENNReal.ofReal_rpow_of_nonneg hbase hexp] at hbound
  change finitePositivePowerTrace (finiteRenyiSandwich R S (1 / 2)) 2 ≤
    finitePositivePowerTrace (finiteRenyiSandwich R S (gaussianRenyiTau r)) r ^
      (1 / (r - 1)) at hbound
  have htwo := finiteBasisCompression_eq_finiteRenyiSandwich b f hfinj hσ.1 hσ.2.2 ha
    (by norm_num : (0 : ℝ) < 1 / 2) hfΞ
  have hhigh := finiteBasisCompression_eq_finiteRenyiSandwich b f hfinj hσ.1 hσ.2.2 ha
    (gaussianRenyiTau_pos hr₁) hfΘ
  change finiteRenyiSandwich R S (1 / 2) = _ at htwo
  change finiteRenyiSandwich R S (gaussianRenyiTau r) = _ at hhigh
  rw [htwo, hhigh] at hbound
  exact hbound.trans (ENNReal.rpow_le_rpow
    (finiteBasisCompression_power_trace_le b f hfinj hcΘ hΘ (by linarith)) hexp)

theorem lowerPowerSandwich_semidefinite_square_trace_bound (b : HilbertBasis ι ℂ E)
    {ρ σ Θ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1) (hσ : IsFaithfulDensity σ)
    {a : ι → ℝ} (ha : ∀ j, σ (b j) = a j • b j) {r : ℝ} (hr : 2 ≤ r)
    (hΘ : 0 ≤ Θ) (hcΘ : IsCompactOperator Θ)
    (hfΘ : σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ) :
    positiveTrace ((lowerPowerSandwich σ Θ (gaussianRenyiTau r) (1 / 2)) ^ (2 : ℝ)) ≤
      positiveTrace (Θ ^ r) ^ (1 / (r - 1)) := by
  classical
  apply positiveTrace_square_le_of_finite_compressions b (lowerPowerSandwich_nonneg hΘ _ _)
  intro s
  exact finite_spectral_semidefinite_sandwich_square_bound b (fun i : s =>
    (i : ι)) Subtype.val_injective
    hρ hρt hσ ha hr hΘ hcΘ hfΘ
    (lowerPowerSandwich_factorization hσ.1 (by norm_num) (gaussianRenyiTau_ge_half hr) hfΘ)

/-- Actual full Hilbert-space interpolation for a positive trace-one input
and faithful reference, including infinite Qr. -/
theorem sandwichedRenyi_interpolation {ρ σ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1) (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 2 ≤ r) :
    sandwichedRenyiQuantity ρ σ 2 ≤ sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) := by
  have hr₁ : 1 < r := by linarith
  by_cases hQ : sandwichedRenyiQuantity ρ σ r = ∞
  · rw [hQ, ENNReal.top_rpow_of_pos (one_div_pos.mpr (sub_pos.mpr hr₁))]
    exact le_top
  have hext : ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
      σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ := by
    by_contra hn
    exact hQ (sandwichedRenyiQuantity_eq_top_of_no_extension hn)
  obtain ⟨Θ, hΘ, hfΘ⟩ := hext
  have hQt := sandwichedRenyiQuantity_eq_power_trace hσ hr₁ hΘ hfΘ
  have htΘ : positiveTrace (Θ ^ r) < ∞ := by
    rw [← hQt]
    exact lt_top_iff_ne_top.mpr hQ
  have hcΘ := isCompactOperator_of_finite_positive_power_trace hΘ
    (lt_trans zero_lt_one hr₁) htΘ
  have hcσ := positiveTraceClass_isCompactOperator hσ.isPositiveTraceClass
  let b := compactSelfAdjointBasis hcσ hσ.1.isSelfAdjoint
  have heig (j : operatorEigenIndex σ) : σ (b j) = j.1.re • b j := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcσ hσ.1.isSelfAdjoint j
  rw [hQt, renyiTwo_lowerPowerSandwich hσ hr hΘ hfΘ]
  exact lowerPowerSandwich_semidefinite_square_trace_bound b hρ hρt hσ heig hr hΘ hcΘ hfΘ


/-- The manuscript trace-distance bound for actual positive trace-one input
and faithful reference, with the full extended trace norm and Renyi quantity. -/
theorem renyi_trace_distance {ρ σ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) (hρt : positiveTrace ρ = 1) (hσ : IsFaithfulDensity σ)
    {r : ℝ} (hr : 2 ≤ r) :
    operatorTraceNorm (ρ - σ) ≤
      (sandwichedRenyiQuantity ρ σ r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) := by
  exact (renyiTwo_trace_distance hσ hρt).trans (ENNReal.rpow_le_rpow
    (tsub_le_tsub_right (sandwichedRenyi_interpolation hρ hρt hσ hr) 1) (by norm_num))

end VacuumBellSeparation.Gaussian
