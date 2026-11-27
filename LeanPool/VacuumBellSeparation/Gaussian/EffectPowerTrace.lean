/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTracePowerOrder
public import LeanPool.VacuumBellSeparation.Gaussian.CompactPositivePowers
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceOrder

/-!
# The source effect power-trace estimate

For an actual compact positive reference sigma and 0<tau<=1, cyclic
positive power traces and contraction concavity give
Tr((sigma^(tau/2) M sigma^(tau/2))^(1/tau)) <= Tr(sqrt(M) sigma sqrt(M)).
M is an arbitrary bounded effect. No commutation or inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Sandwich an effect between two half-powers of the reference density. -/
def referenceEffectPower (σ M : E →L[ℂ] E) (τ : ℝ) : E →L[ℂ] E :=
  σ ^ (τ / 2) * M * σ ^ (τ / 2)

theorem referenceEffectPower_nonneg {σ M : E →L[ℂ] E} (hM : 0 ≤ M) (τ : ℝ) :
    0 ≤ referenceEffectPower σ M τ :=
  conjugate_nonneg_of_nonneg hM CFC.rpow_nonneg

theorem referenceEffectPower_isCompactOperator {σ M : E →L[ℂ] E}
    (hcσ : IsCompactOperator σ) (hσ : 0 ≤ σ) {τ : ℝ} (hτ : 0 < τ) :
    IsCompactOperator (referenceEffectPower σ M τ) := by
  have hR := isCompactOperator_positive_rpow hcσ hσ (half_pos hτ)
  exact (hR.clm_comp M).clm_comp (σ ^ (τ / 2))

theorem referenceEffectPower_trace_bound {σ M : E →L[ℂ] E}
    (hcσ : IsCompactOperator σ) (hσ : 0 ≤ σ) (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1)
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) :
    positiveTrace (referenceEffectPower σ M τ ^ (1 / τ : ℝ)) ≤
      positiveTrace (CFC.sqrt M * σ * CFC.sqrt M) := by
  let R := σ ^ (τ / 2)
  let X := CFC.sqrt M * σ ^ τ * CFC.sqrt M
  let Y := CFC.sqrt M * σ * CFC.sqrt M
  let T := CFC.sqrt M * R
  have hR : 0 ≤ R := CFC.rpow_nonneg
  have hRR : R * R = σ ^ τ := by
    dsimp only [R]
    rw [← positiveOperator_rpow_add_nonneg hσ (half_pos hτ₀).le (half_pos hτ₀).le,
      add_halves]
  have hT₁ : star T * T = referenceEffectPower σ M τ := by
    dsimp only [T, referenceEffectPower]
    rw [star_mul, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq]
    calc
      _ = R * (CFC.sqrt M * CFC.sqrt M) * R := by noncomm_ring
      _ = _ := by rw [← pow_two, CFC.sq_sqrt M hM₀]
  have hT₂ : T * star T = X := by
    dsimp only [T, X]
    rw [star_mul, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq]
    calc
      _ = CFC.sqrt M * (R * R) * CFC.sqrt M := by noncomm_ring
      _ = _ := by rw [hRR]
  have hq : 1 ≤ 1 / τ := (le_div_iff₀ hτ₀).mpr (by simpa using hτ₁)
  have hcyc := positiveTrace_star_mul_self_rpow T
    (hT₁.symm ▸ referenceEffectPower_isCompactOperator hcσ hσ hτ₀) hq
  rw [hT₁, hT₂] at hcyc
  have hcX : IsCompactOperator X :=
    ((isCompactOperator_positive_rpow hcσ hσ hτ₀).comp_clm (CFC.sqrt M)).clm_comp (CFC.sqrt M)
  have hX : 0 ≤ X := conjugate_nonneg_of_nonneg CFC.rpow_nonneg (CFC.sqrt_nonneg M)
  have hY : 0 ≤ Y := conjugate_nonneg_of_nonneg hσ (CFC.sqrt_nonneg M)
  have hXY : X ≤ Y ^ τ := effect_sqrt_rpow_le hM₀ hM₁ hσ hτ₀ hτ₁
  rw [hcyc]
  calc
    _ ≤ positiveTrace ((Y ^ τ) ^ (1 / τ : ℝ)) := positiveTrace_rpow_mono hcX hX hXY hq
    _ = _ := by
      rw [CFC.rpow_rpow_of_exponent_nonneg Y τ (1 / τ) hτ₀.le
        (one_div_pos.mpr hτ₀).le hY, mul_one_div_cancel hτ₀.ne', CFC.rpow_one Y hY]

theorem positiveTrace_effect_le {σ M : E →L[ℂ] E}
    (hσ : 0 ≤ σ) (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) :
    positiveTrace (CFC.sqrt M * σ * CFC.sqrt M) ≤ positiveTrace σ := by
  rw [positiveTrace_sqrt_sandwich_swap hM₀ hσ]
  have hle : CFC.sqrt σ * M * CFC.sqrt σ ≤ σ := by
    have h := (CFC.sqrt_nonneg σ).isSelfAdjoint.conjugate_nonneg (sub_nonneg.mpr hM₁)
    have heq : CFC.sqrt σ * (1 - M) * CFC.sqrt σ =
        σ - CFC.sqrt σ * M * CFC.sqrt σ := by
      rw [mul_sub, sub_mul, mul_one, ← pow_two, CFC.sq_sqrt σ hσ]
    rw [heq] at h
    exact sub_nonneg.mp h
  exact positiveTrace_mono (conjugate_nonneg_of_nonneg hM₀ (CFC.sqrt_nonneg σ)) hle

end VacuumBellSeparation.Gaussian
