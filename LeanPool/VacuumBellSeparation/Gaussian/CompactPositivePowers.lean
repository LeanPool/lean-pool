/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactPowerIntertwining

/-!
# Compactness of genuine positive functional-calculus powers

The zero-preserving continuous functional calculus of a compact
self-adjoint operator stays compact, by Stone--Weierstrass induction and
operator-norm closedness. Thus every positive power of a compact positive
operator is compact. Conversely a finite positive power trace implies
compactness of the original positive operator.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter
open scoped Topology ENNReal ContinuousFunctionalCalculus ContinuousMapZero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isCompactOperator_cfcₙHom {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : IsSelfAdjoint A) (f : C(quasispectrum ℝ A, ℝ)₀) :
    IsCompactOperator (cfcₙHom hA f) := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa only [map_zero, FunLike.coe_zero] using
      (isCompactOperator_zero : IsCompactOperator (0 : E → E))
  | id => simpa only [cfcₙHom_id] using hc
  | star_id => simpa only [map_star, cfcₙHom_id, hA.star_eq] using hc
  | add f g hf hg => simpa only [map_add, FunLike.coe_add] using hf.add hg
  | mul f g hf hg =>
    rw [map_mul]
    exact hf.comp_clm (cfcₙHom hA g)
  | smul r f hf => simpa only [map_smul, FunLike.coe_smul] using hf.smul r
  | frequently f hf =>
    exact (isClosed_setOfPred_isCompactOperator.preimage
      (cfcₙHom_continuous hA)).mem_of_frequently_of_tendsto
      hf tendsto_id

theorem isCompactOperator_cfcₙ {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : IsSelfAdjoint A) (f : ℝ → ℝ) (hf : ContinuousOn f (quasispectrum ℝ A))
    (hf₀ : f 0 = 0) : IsCompactOperator (cfcₙ (A := E →L[ℂ] E) f A) := by
  rw [cfcₙ_apply (A := E →L[ℂ] E) f A hf hf₀ hA]
  exact isCompactOperator_cfcₙHom hc hA _

theorem isCompactOperator_positive_rpow {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) : IsCompactOperator (A ^ p) := by
  have hf : Continuous (fun x : ℝ => x ^ p) := Real.continuous_rpow_const hp.le
  have hf₀ : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp.ne'
  rw [CFC.rpow_eq_cfc_real hA, ← cfcₙ_eq_cfc hf.continuousOn hf₀]
  exact isCompactOperator_cfcₙ hc hA.isSelfAdjoint _ hf.continuousOn hf₀

theorem isCompactOperator_of_positive_rpow {A : E →L[ℂ] E}
    (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) (hc : IsCompactOperator (A ^ p)) :
    IsCompactOperator A := by
  have h := isCompactOperator_positive_rpow hc CFC.rpow_nonneg (one_div_pos.mpr hp)
  rwa [CFC.rpow_rpow_of_exponent_nonneg A p (1 / p) hp.le (one_div_pos.mpr hp).le hA,
    mul_one_div_cancel hp.ne', CFC.rpow_one A hA] at h

theorem isCompactOperator_of_finite_positive_power_trace {A : E →L[ℂ] E}
    (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) (ht : positiveTrace (A ^ p) < ∞) :
    IsCompactOperator A :=
  isCompactOperator_of_positive_rpow hA hp
    (positiveTraceClass_isCompactOperator ⟨CFC.rpow_nonneg, ht⟩)

end VacuumBellSeparation.Gaussian
