/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.NuclearNormConvergence

/-!
# Constructing a reserve factor from its nuclear series

Termwise factorizations and a finite actual nuclear sum construct a
bounded compact self-adjoint factor. Multiplication of the actual
operator-norm sums then identifies the full covariance operator.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem hasSum_sandwiched_operator_series {Z : ι → E →L[ℂ] E}
    (hs : Summable Z) (R : E →L[ℂ] E) :
    HasSum (fun i => R * Z i * R) (R * (∑' i, Z i) * R) :=
  (hs.hasSum.mul_left R).mul_right R

theorem exists_reserve_factor_of_nuclear_series
    {G Z : ι → E →L[ℂ] E} {D : E →L[ℂ] E} (R : E →L[ℂ] E)
    (hG : HasSum G D) (hfactor : ∀ i, G i = R * Z i * R)
    (hcZ : ∀ i, IsCompactOperator (Z i)) (hZ : ∀ i, IsSelfAdjoint (Z i))
    (ht : (∑' i, operatorTraceNorm (Z i)) < ∞) :
    ∃ Y : E →L[ℂ] E, D = R * Y * R ∧ IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
      operatorTraceNorm Y ≤ ∑' i, operatorTraceNorm (Z i) ∧
      operatorTraceNorm Y < ∞ := by
  obtain ⟨hs, hc, hsa, hbound⟩ := nuclear_sum_constructs_compact_selfAdjoint hcZ hZ ht
  have hfun : HasSum (fun i => (Z i : E → E))
      (fun x => ((∑' i, Z i) : E →L[ℂ] E) x) := by
    apply Pi.hasSum.mpr
    intro x
    exact (ContinuousLinearMap.apply ℂ E x).hasSum hs.hasSum
  rw [hfun.tsum_eq] at hc
  refine ⟨∑' i, Z i, ?_, hc, hsa, hbound, hbound.trans_lt ht⟩
  have hsum := hasSum_sandwiched_operator_series hs R
  have hG' : HasSum (fun i => R * Z i * R) D :=
    hG.congr_fun (fun i => (hfactor i).symm)
  exact hG'.unique hsum

end VacuumBellSeparation.Gaussian
