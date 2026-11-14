/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# AESummability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Almost-everywhere summability from stretched-exponential layer bounds

The real-valued `tsum` of a nonsummable fiber is zero, whereas the
corresponding sum is infinite.  Consequently a weak-Orlicz estimate for the
real `tsum` alone does not identify the actual nonnegative extended-real
envelope.

This file supplies the missing analytic bridge.  If nonnegative layers have
`Gamma_sigma` bounds at a summable family of positive scales, their first
moments are summable.  Tonelli's theorem then gives pointwise summability
almost everywhere, and the usual `ENNReal.ofReal_tsum_of_nonneg` identity is available
on that full-measure set.

These are general analytic Provider lemmas.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A summable family of positive `Gamma_sigma` scales forces a nonnegative
family of random variables to be summable almost everywhere. -/
theorem ae_summable_of_isBigOWith_gammaSigma
    [IsProbabilityMeasure mu]
    {X : ℕ → Omega → ℝ} {a : ℕ → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hX_meas : ∀ n, AEMeasurable (X n) mu)
    (ha : ∀ n, 0 < a n)
    (ha_summable : Summable a)
    (hX : ∀ n, IsBigOWith mu (gammaSigma sigma) (X n) (a n)) :
    ∀ᵐ omega ∂mu, Summable fun n => X n omega := by
  have hX_integrable : ∀ n, Integrable (X n) mu := by
    intro n
    have hint := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := X n) (K := a n) (σ := sigma) (p := 1)
      hsigma (ha n) (by norm_num) (hX_nonneg n) (hX_meas n) (hX n)
    simpa only [Real.rpow_one] using hint
  have hintegral_le : ∀ n,
      ∫ omega, ‖X n omega‖ ∂mu ≤ gammaMomentConst sigma * a n := by
    intro n
    have hmoment := integral_rpow_le_of_isBigOWith_gammaSigma
      (μ := mu) (Y := X n) (K := a n) (σ := sigma) (p := 1)
      hsigma (ha n) (by norm_num) (hX_nonneg n) (hX_meas n) (hX n)
    have hnorm : (fun omega => ‖X n omega‖) = X n := by
      funext omega
      exact Real.norm_of_nonneg (hX_nonneg n omega)
    rw [hnorm]
    simpa only [Real.rpow_one, Real.one_rpow, mul_one] using hmoment
  have hintegral_summable :
      Summable fun n => ∫ omega, ‖X n omega‖ ∂mu := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _)
      hintegral_le ?_
    exact ha_summable.mul_left (gammaMomentConst sigma)
  have henorm_meas : ∀ n,
      AEMeasurable (fun omega => ‖X n omega‖ₑ) mu := by
    intro n
    exact (hX_integrable n).1.enorm
  have hlintegral_sum :
      (∑' n, ∫⁻ omega, ‖X n omega‖ₑ ∂mu) ≠ (⊤ : ENNReal) := by
    have hlintegral_eq (n : ℕ) :
        ∫⁻ omega, ‖X n omega‖ₑ ∂mu =
          ‖∫ omega, ‖X n omega‖ ∂mu‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hX_integrable n).norm]
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      rw [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun omega => by
          simp [abs_nonneg (X n omega)])]
      rfl
    rw [funext hlintegral_eq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hintegral_summable.abs)
  have htotal_lintegral :
      ∫⁻ omega, ∑' n, ‖X n omega‖ₑ ∂mu ≠ (⊤ : ENNReal) := by
    rw [lintegral_tsum henorm_meas]
    exact hlintegral_sum
  refine (ae_lt_top' (AEMeasurable.tsum (L := SummationFilter.unconditional ℕ) henorm_meas)
    htotal_lintegral).mono ?_
  intro omega homega
  have hnorm_summable : Summable fun n => ‖X n omega‖ := by
    have hnnreal :
        Summable fun n => ((‖X n omega‖₊ : NNReal) : ℝ) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      simpa only [enorm_eq_nnnorm] using homega.ne
    simpa only [coe_nnnorm] using hnnreal
  have hnorm_eq : (fun n => ‖X n omega‖) = fun n => X n omega := by
    funext n
    exact Real.norm_of_nonneg (hX_nonneg n omega)
  rw [hnorm_eq] at hnorm_summable
  exact hnorm_summable

end

end Algsuperdiff.Section3.Provider.Orlicz
