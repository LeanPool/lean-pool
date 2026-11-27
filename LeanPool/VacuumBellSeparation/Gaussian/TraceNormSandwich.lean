/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm

/-!
# The genuine Schatten (4,2,4) sandwich estimate

For a compact self-adjoint K and compact positive B, diagonal order
bounds and actual positive Schatten Holder prove
||sqrt(B) K sqrt(B)||_1 <= Tr(K^2)^(1/2) Tr(B^2)^(1/2).
All traces are extended values on the actual Hilbert space.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operatorTraceNorm_sqrt_sandwich_le {K B : E →L[ℂ] E}
    (hcK : IsCompactOperator K) (hK : IsSelfAdjoint K)
    (hcB : IsCompactOperator B) (hB : 0 ≤ B) :
    operatorTraceNorm (CFC.sqrt B * K * CFC.sqrt B) ≤
      positiveTrace (K * K) ^ (1 / 2 : ℝ) * positiveTrace (B * B) ^ (1 / 2 : ℝ) := by
  let R := CFC.sqrt B
  have hR : IsSelfAdjoint R := (CFC.sqrt_nonneg B).isSelfAdjoint
  have hc : IsCompactOperator (R * K * R) := (hcK.clm_comp R).comp_clm R
  have hl : -(R * CFC.abs K * R) ≤ R * K * R := by
    have h := hR.conjugate_nonneg (operator_abs_add_nonneg hK)
    rw [mul_add, add_mul] at h
    exact neg_le_iff_add_nonneg'.mpr h
  have hu : R * K * R ≤ R * CFC.abs K * R := by
    have h := hR.conjugate_nonneg (operator_abs_sub_nonneg hK)
    rw [mul_sub, sub_mul] at h
    exact sub_nonneg.mp h
  have ht := operatorTraceNorm_le_positiveTrace_of_order_bounds hc (hK.conjugate_self hR)
    (hR.conjugate_nonneg (CFC.abs_nonneg K)) hl hu
  have hh := positiveTrace_sandwich_holder (isCompactOperator_abs hcK hK) hcB
    (CFC.abs_nonneg K) hB Real.HolderConjugate.two_two
  have ha : CFC.abs K ^ (2 : ℝ) = K * K := by
    calc
      _ = CFC.abs K ^ (2 : ℕ) := by
        simpa only [Nat.cast_ofNat] using CFC.rpow_natCast (CFC.abs K) 2 (CFC.abs_nonneg K)
      _ = _ := by rw [pow_two, CFC.abs_mul_abs, hK.star_eq]
  have hb : B ^ (2 : ℝ) = B * B := by
    simpa only [Nat.cast_ofNat, pow_two] using CFC.rpow_natCast B 2 hB
  rw [ha, hb] at hh
  exact ht.trans hh

theorem operatorTraceNorm_sqrt_sandwich_lt_top {K B : E →L[ℂ] E}
    (hcK : IsCompactOperator K) (hK : IsSelfAdjoint K)
    (hcB : IsCompactOperator B) (hB : 0 ≤ B)
    (htK : positiveTrace (K * K) < ∞) (htB : positiveTrace (B * B) < ∞) :
    operatorTraceNorm (CFC.sqrt B * K * CFC.sqrt B) < ∞ := by
  apply (operatorTraceNorm_sqrt_sandwich_le hcK hK hcB hB).trans_lt
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) htK.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) htB.ne)

end VacuumBellSeparation.Gaussian
