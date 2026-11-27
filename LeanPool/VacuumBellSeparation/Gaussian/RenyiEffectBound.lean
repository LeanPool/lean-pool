/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveEffectExpectationDefs
public import LeanPool.VacuumBellSeparation.Gaussian.EffectPowerTrace
public import LeanPool.VacuumBellSeparation.Gaussian.SandwichedRenyiQuantity
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveDensityState

/-!
# The actual arbitrary-effect bound from a finite sandwiched Rényi quantity

The expectation is the actual positive square-root sandwich trace. It
agrees with the previously constructed density state. Positive Schatten
Hölder and the effect power estimate prove the manuscript inequality for
arbitrary bounded effects, with no Gaussian or commutation restriction.
The finite-quantity theorem derives the genuine factorization from the
quantity definition and does not assume an inverse or a trace-class Theta.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]



theorem positiveEffectExpectation_eq_densityExpectation (b : HilbertBasis ι ℂ E)
    {ρ M : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hM : 0 ≤ M) :
    positiveEffectExpectation ρ M = ENNReal.ofReal (densityExpectation b ρ M).re := by
  rw [positiveEffectExpectation, positiveTrace_sqrt_sandwich_swap hM hρ.1]
  exact positiveTrace_density_sandwich b hρ hM

theorem positiveEffectExpectation_factorization {ρ Θ R M : E →L[ℂ] E}
    (hΘ : 0 ≤ Θ) (hR : IsSelfAdjoint R) (hM : 0 ≤ M) (hf : R * Θ * R = ρ) :
    positiveEffectExpectation ρ M = positiveTrace (CFC.sqrt Θ * (R * M * R) * CFC.sqrt Θ) := by
  let T := CFC.sqrt Θ * R * CFC.sqrt M
  have hT₁ : T.adjoint.comp T = CFC.sqrt M * ρ * CFC.sqrt M := by
    change star (CFC.sqrt Θ * R * CFC.sqrt M) * (CFC.sqrt Θ * R * CFC.sqrt M) = _
    rw [star_mul, star_mul, (CFC.sqrt_nonneg Θ).isSelfAdjoint.star_eq, hR.star_eq,
      (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    calc
      _ = CFC.sqrt M * (R * (CFC.sqrt Θ * CFC.sqrt Θ) * R) * CFC.sqrt M := by noncomm_ring
      _ = _ := by rw [← pow_two, CFC.sq_sqrt Θ hΘ, hf]
  have hT₂ : T.comp T.adjoint = CFC.sqrt Θ * (R * M * R) * CFC.sqrt Θ := by
    change (CFC.sqrt Θ * R * CFC.sqrt M) * star (CFC.sqrt Θ * R * CFC.sqrt M) = _
    rw [star_mul, star_mul, (CFC.sqrt_nonneg Θ).isSelfAdjoint.star_eq, hR.star_eq,
      (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    calc
      _ = CFC.sqrt Θ * (R * (CFC.sqrt M * CFC.sqrt M) * R) * CFC.sqrt Θ := by noncomm_ring
      _ = _ := by rw [← pow_two, CFC.sq_sqrt M hM]
  rw [positiveEffectExpectation, ← hT₁, positiveTrace_adjoint_comp_eq_comp_adjoint, hT₂]

theorem gaussianRenyiTau_holderConjugate {r : ℝ} (hr : 1 < r) :
    r.HolderConjugate (1 / gaussianRenyiTau r) := by
  apply Real.holderConjugate_iff.mpr
  refine ⟨hr, ?_⟩
  rw [one_div, inv_inv]
  unfold gaussianRenyiTau
  field_simp [ne_of_gt (show 0 < r by linarith)]
  ring

theorem renyi_effect_bound_of_factorization {ρ σ Θ M : E →L[ℂ] E}
    (hσ : IsPositiveTraceClass σ) {r : ℝ} (hr : 1 < r) (hΘ : 0 ≤ Θ)
    (htrace : positiveTrace (Θ ^ r) < ∞)
    (hf : σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ)
    (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) :
    positiveEffectExpectation ρ M ^ r ≤
      positiveTrace (Θ ^ r) * positiveEffectExpectation σ M ^ (r - 1) := by
  have hr₀ : 0 < r := lt_trans zero_lt_one hr
  have hτ₀ := gaussianRenyiTau_pos hr
  have hτ₁ := (gaussianRenyiTau_lt_one hr).le
  let B := referenceEffectPower σ M (gaussianRenyiTau r)
  have hB : 0 ≤ B := referenceEffectPower_nonneg hM₀ _
  have hcσ := positiveTraceClass_isCompactOperator hσ
  have hcB : IsCompactOperator B := referenceEffectPower_isCompactOperator hcσ hσ.1 hτ₀
  have hcΘ := isCompactOperator_of_finite_positive_power_trace hΘ hr₀ htrace
  have hhold := positiveTrace_sandwich_holder hcΘ hcB hΘ hB
    (gaussianRenyiTau_holderConjugate hr)
  have hleft : positiveEffectExpectation ρ M = positiveTrace (CFC.sqrt B * Θ * CFC.sqrt B) := by
    calc
      _ = positiveTrace (CFC.sqrt Θ * B * CFC.sqrt Θ) := by
        simpa only [B, referenceEffectPower] using
          positiveEffectExpectation_factorization hΘ CFC.rpow_nonneg.isSelfAdjoint hM₀ hf
      _ = _ := positiveTrace_sqrt_sandwich_swap hΘ hB
  rw [← hleft, one_div_one_div] at hhold
  have hbtrace : positiveTrace (B ^ (1 / gaussianRenyiTau r : ℝ)) ≤
      positiveEffectExpectation σ M := referenceEffectPower_trace_bound hcσ hσ.1 hM₀ hM₁ hτ₀ hτ₁
  have h := hhold.trans (_root_.mul_le_mul_right
    (ENNReal.rpow_le_rpow hbtrace hτ₀.le) (positiveTrace (Θ ^ r) ^ (1 / r)))
  have hpower := ENNReal.rpow_le_rpow h hr₀.le
  have hτr : gaussianRenyiTau r * r = r - 1 := by
    unfold gaussianRenyiTau
    exact div_mul_cancel₀ _ hr₀.ne'
  rwa [ENNReal.mul_rpow_of_nonneg _ _ hr₀.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr₀.ne', ENNReal.rpow_one, ← ENNReal.rpow_mul, hτr] at hpower

theorem finite_sandwichedRenyi_effect_bound {ρ σ M : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 1 < r)
    (hQ : sandwichedRenyiQuantity ρ σ r < ∞) (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) :
    positiveEffectExpectation ρ M ^ r ≤
      sandwichedRenyiQuantity ρ σ r * positiveEffectExpectation σ M ^ (r - 1) := by
  have hext : ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
      σ ^ (gaussianRenyiTau r / 2) * Θ * σ ^ (gaussianRenyiTau r / 2) = ρ := by
    by_contra hn
    rw [sandwichedRenyiQuantity_eq_top_of_no_extension hn] at hQ
    exact lt_irrefl _ hQ
  obtain ⟨Θ, hΘ, hf⟩ := hext
  have hq := sandwichedRenyiQuantity_eq_power_trace hσ hr hΘ hf
  rw [hq] at hQ ⊢
  exact renyi_effect_bound_of_factorization
    ⟨hσ.1, by rw [hσ.2.1]; exact ENNReal.one_lt_top⟩ hr hΘ hQ hf hM₀ hM₁

end VacuumBellSeparation.Gaussian
