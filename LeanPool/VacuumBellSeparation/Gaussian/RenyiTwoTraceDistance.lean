/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveSquareDifferenceTrace
public import LeanPool.VacuumBellSeparation.Gaussian.FaithfulRenyiEffectBound

/-!
# The actual r=2 trace-distance consequence

The centered Hilbert--Schmidt identity and the actual (4,2,4) Schatten
estimate give the manuscript trace-distance bound at r=2. The inverse
sandwich is the genuine bounded extension on the dense inverse-power
range, derived from finite Q_2. No bounded inverse or finite-dimensional
substitute is introduced.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveTrace_centered_density_square {ρ σ Θ : E →L[ℂ] E}
    (hσ : 0 ≤ σ) (hσt : positiveTrace σ = 1) (hρt : positiveTrace ρ = 1)
    (hcΘ : IsCompactOperator Θ) (hΘ : 0 ≤ Θ)
    (hf : CFC.sqrt (CFC.sqrt σ) * Θ * CFC.sqrt (CFC.sqrt σ) = ρ) :
    positiveTrace ((Θ - CFC.sqrt σ) * (Θ - CFC.sqrt σ)) + 1 =
      positiveTrace (Θ * Θ) := by
  have hs : CFC.sqrt σ * CFC.sqrt σ = σ := by rw [← pow_two, CFC.sq_sqrt σ hσ]
  have h := positiveTrace_square_difference_add hcΘ hΘ (CFC.sqrt_nonneg σ)
  rw [hf, hs, hσt, hρt] at h
  apply (ENNReal.add_left_inj ENNReal.one_ne_top).mp
  simpa only [add_assoc, one_add_one_eq_two, mul_one] using h

theorem sqrt_sqrt_eq_renyiTwo_power {σ : E →L[ℂ] E} (hσ : 0 ≤ σ) :
    CFC.sqrt (CFC.sqrt σ) = σ ^ (gaussianRenyiTau 2 / 2) := by
  rw [CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow,
    CFC.rpow_rpow_of_exponent_nonneg σ (1 / 2) (1 / 2) (by norm_num) (by norm_num) hσ]
  norm_num [gaussianRenyiTau]

theorem renyiTwo_trace_distance_of_factorization {ρ σ Θ : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) (hρt : positiveTrace ρ = 1)
    (hΘ : 0 ≤ Θ) (htΘ : positiveTrace (Θ ^ (2 : ℝ)) < ∞)
    (hf : σ ^ (gaussianRenyiTau 2 / 2) * Θ * σ ^ (gaussianRenyiTau 2 / 2) = ρ) :
    operatorTraceNorm (ρ - σ) ≤ (positiveTrace (Θ ^ (2 : ℝ)) - 1) ^ (1 / 2 : ℝ) := by
  let S := CFC.sqrt σ
  let K := Θ - S
  have hS : 0 ≤ S := CFC.sqrt_nonneg σ
  have hcσ := positiveTraceClass_isCompactOperator hσ.isPositiveTraceClass
  have hcS : IsCompactOperator S := by
    dsimp only [S]
    rw [CFC.sqrt_eq_rpow]
    exact isCompactOperator_positive_rpow hcσ hσ.1 (by norm_num)
  have hcΘ := isCompactOperator_of_finite_positive_power_trace hΘ (by norm_num : (0 : ℝ) < 2) htΘ
  have hK : IsSelfAdjoint K := hΘ.isSelfAdjoint.sub hS.isSelfAdjoint
  have hcK : IsCompactOperator K := hcΘ.sub hcS
  have hf' : CFC.sqrt S * Θ * CFC.sqrt S = ρ := by
    simpa only [S, sqrt_sqrt_eq_renyiTwo_power hσ.1] using hf
  have hSS : S * S = σ := by dsimp only [S]; rw [← pow_two, CFC.sq_sqrt σ hσ.1]
  have hfactor : CFC.sqrt S * K * CFC.sqrt S = ρ - σ := by
    dsimp only [K]
    rw [mul_sub, sub_mul, hf']
    congr 1
    calc
      CFC.sqrt S * S * CFC.sqrt S =
          (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S * CFC.sqrt S) := by
        calc
          _ = CFC.sqrt S * (CFC.sqrt S * CFC.sqrt S) * CFC.sqrt S :=
            congrArg (fun X : E →L[ℂ] E => CFC.sqrt S * X * CFC.sqrt S)
              (CFC.sqrt_mul_sqrt_self S hS).symm
          _ = _ := by noncomm_ring
      _ = σ := by rw [CFC.sqrt_mul_sqrt_self S hS, hSS]
  have hcenter := positiveTrace_centered_density_square hσ.1 hσ.2.1 hρt hcΘ hΘ hf'
  have hpow : Θ ^ (2 : ℝ) = Θ * Θ := by
    simpa only [Nat.cast_ofNat, pow_two] using
      (CFC.rpow_natCast (A := E →L[ℂ] E) Θ 2 hΘ)
  have hcenter' : positiveTrace (K * K) = positiveTrace (Θ ^ (2 : ℝ)) - 1 := by
    rw [hpow, ← hcenter]
    exact (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm
  have hb := operatorTraceNorm_sqrt_sandwich_le hcK hK hcS hS
  rw [hfactor, hSS, hσ.2.1, ENNReal.one_rpow, mul_one, hcenter'] at hb
  exact hb

theorem finite_renyiTwo_trace_distance {ρ σ : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) (hρt : positiveTrace ρ = 1)
    (hQ : sandwichedRenyiQuantity ρ σ 2 < ∞) :
    operatorTraceNorm (ρ - σ) ≤
      (sandwichedRenyiQuantity ρ σ 2 - 1) ^ (1 / 2 : ℝ) := by
  have hext : ∃ Θ : E →L[ℂ] E, 0 ≤ Θ ∧
      σ ^ (gaussianRenyiTau 2 / 2) * Θ * σ ^ (gaussianRenyiTau 2 / 2) = ρ := by
    by_contra hn
    rw [sandwichedRenyiQuantity_eq_top_of_no_extension hn] at hQ
    exact lt_irrefl _ hQ
  obtain ⟨Θ, hΘ, hf⟩ := hext
  have hq := sandwichedRenyiQuantity_eq_power_trace hσ (by norm_num : (1 : ℝ) < 2) hΘ hf
  rw [hq] at hQ ⊢
  exact renyiTwo_trace_distance_of_factorization hσ hρt hΘ hQ hf

/-- Extended-valued r=2 endpoint, including infinite Q without any
subtraction of real infinities. -/
theorem renyiTwo_trace_distance {ρ σ : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) (hρt : positiveTrace ρ = 1) :
    operatorTraceNorm (ρ - σ) ≤
      (sandwichedRenyiQuantity ρ σ 2 - 1) ^ (1 / 2 : ℝ) := by
  by_cases hQ : sandwichedRenyiQuantity ρ σ 2 = ∞
  · rw [hQ, ENNReal.top_sub ENNReal.one_ne_top, ENNReal.top_rpow_of_pos (by norm_num)]
    exact le_top
  · exact finite_renyiTwo_trace_distance hσ hρt (lt_top_iff_ne_top.mpr hQ)

end VacuumBellSeparation.Gaussian
