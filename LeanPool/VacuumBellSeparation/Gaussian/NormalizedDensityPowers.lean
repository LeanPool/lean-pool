/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceScaling
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumPurityCalculus

/-!
# Actual positive powers and normalization of density operators

The scalar power law is derived from the genuine continuous functional
calculus. Trace normalization then separates the actual logarithmic power
trace into the partition term and the normalized density term, only after
strict positivity and finiteness of the relevant traces have been proved.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveOperator_real_smul_rpow {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    (c • A) ^ r = c ^ r • (A ^ r) := by
  have hf : Continuous (fun x : ℝ => x ^ r) := Real.continuous_rpow_const hr
  rw [CFC.rpow_eq_cfc_real (smul_nonneg hc hA), CFC.rpow_eq_cfc_real hA,
    ← cfc_comp_const_mul c (fun x : ℝ => x ^ r) A hf.continuousOn hA.isSelfAdjoint]
  calc
    _ = cfc (fun x : ℝ => c ^ r * x ^ r) A :=
      cfc_congr fun x hx => Real.mul_rpow hc (spectrum_nonneg_of_nonneg hA hx)
    _ = _ := cfc_const_mul (c ^ r) (fun x : ℝ => x ^ r) A hf.continuousOn

theorem positiveDensity_eq_trace_smul_normalized {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (ht : 0 < positiveTrace A) :
    A = (positiveTrace A).toReal • normalizedPositiveDensity A := by
  have hr : (positiveTrace A).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.ne' hA.2.ne).ne'
  rw [normalizedPositiveDensity, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem positiveDensity_rpow_eq_trace_smul_normalized_rpow {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (ht : 0 < positiveTrace A) {r : ℝ} (hr : 0 ≤ r) :
    A ^ r = (positiveTrace A).toReal ^ r • (normalizedPositiveDensity A ^ r) := by
  conv_lhs => rw [positiveDensity_eq_trace_smul_normalized hA ht]
  exact positiveOperator_real_smul_rpow
    (smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hA.1)
    ENNReal.toReal_nonneg hr

theorem positiveDensity_rpow_trace_pos_finite_of_normalized (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (ht : 0 < positiveTrace A)
    {r : ℝ} (hr : 0 ≤ r)
    (hn : 0 < positiveTrace (normalizedPositiveDensity A ^ r) ∧
      positiveTrace (normalizedPositiveDensity A ^ r) < ⊤) :
    0 < positiveTrace (A ^ r) ∧ positiveTrace (A ^ r) < ⊤ := by
  have hp := Real.rpow_pos_of_pos (ENNReal.toReal_pos ht.ne' hA.2.ne) r
  rw [positiveDensity_rpow_eq_trace_smul_normalized_rpow hA ht hr,
    positiveTrace_real_smul b CFC.rpow_nonneg hp.le]
  exact ⟨bot_lt_iff_ne_bot.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr hp).ne' hn.1.ne'),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn.2⟩

theorem log_positiveTrace_rpow_normalization (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) (ht : 0 < positiveTrace A)
    {r : ℝ} (hr : 0 ≤ r)
    (hn : 0 < positiveTrace (normalizedPositiveDensity A ^ r) ∧
      positiveTrace (normalizedPositiveDensity A ^ r) < ⊤) :
    Real.log (positiveTrace (A ^ r)).toReal =
      r * Real.log (positiveTrace A).toReal +
        Real.log (positiveTrace (normalizedPositiveDensity A ^ r)).toReal := by
  have htR := ENNReal.toReal_pos ht.ne' hA.2.ne
  have hnR := ENNReal.toReal_pos hn.1.ne' hn.2.ne
  rw [positiveDensity_rpow_eq_trace_smul_normalized_rpow hA ht hr,
    positiveTrace_real_smul b CFC.rpow_nonneg (Real.rpow_pos_of_pos htR r).le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_pos_of_pos htR r).le,
    Real.log_mul (Real.rpow_pos_of_pos htR r).ne' hnR.ne', Real.log_rpow htR]

theorem gaussianPhysical_rpow_trace_pos_finite_of_strict_quantum {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hG : HasGaussianPhysicalCharacteristic A V) {r : ℝ} (hr : 0 < r) :
    0 < positiveTrace (A ^ r) ∧ positiveTrace (A ^ r) < ⊤ := by
  obtain ⟨ν, S, hν, hS, hcov⟩ := exists_faithful_canonical_williamson V hV hQ
  rw [← hcov] at hG
  exact gaussianPhysical_rpow_trace_pos_finite hA S hS (fun j => (hν j).le) hG hr

end VacuumBellSeparation.Gaussian
