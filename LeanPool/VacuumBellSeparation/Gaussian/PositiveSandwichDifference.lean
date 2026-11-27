/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteSpectralTraceRecovery
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceScaling

/-!
# A genuine nuclear modulus for positive sandwich differences

Weighted square positivity controls both orders of SAS-TAT. The actual
positive trace ideal bound then gives a modulus tending to zero as S tends
to T. No operator absolute-value monotonicity or finite-rank estimate is
used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem weighted_positive_cross_square {A D T : E →L[ℂ] E}
    (hA : 0 ≤ A) (hD : IsSelfAdjoint D) (hT : IsSelfAdjoint T)
    {η : ℝ} (hη : 0 < η) :
    0 ≤ η⁻¹ • (D * A * D) + η • (T * A * T) - (D * A * T + T * A * D) := by
  have hp := ((hD.sub ((IsSelfAdjoint.all η).smul hT)).conjugate_nonneg hA)
  have hn := smul_nonneg (inv_nonneg.mpr hη.le) hp
  convert hn using 1
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub,
    smul_smul, inv_mul_cancel₀ hη.ne', inv_mul_cancel_left₀ hη.ne', one_smul]
  module

theorem positive_sandwich_difference_order {A S T : E →L[ℂ] E}
    (hA : 0 ≤ A) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    {η : ℝ} (hη : 0 < η) :
    let D := S - T
    let W := (1 + η⁻¹) • (D * A * D) + η • (T * A * T);
    -(W) ≤ S * A * S - T * A * T ∧ S * A * S - T * A * T ≤ W := by
  dsimp only
  let D := S - T
  have hD : IsSelfAdjoint D := hS.sub hT
  have hdiag : 0 ≤ D * A * D := hD.conjugate_nonneg hA
  have he : S * A * S - T * A * T = D * A * D + (D * A * T + T * A * D) := by
    dsimp only [D]
    noncomm_ring
  have hminus := weighted_positive_cross_square hA hD hT hη
  have hplus := weighted_positive_cross_square hA hD hT.neg hη
  simp only [neg_mul, mul_neg, neg_neg] at hplus
  rw [he]
  constructor
  · apply neg_le_iff_add_nonneg'.mpr
    convert add_nonneg (add_nonneg hdiag hdiag) hplus using 1; module
  · apply sub_nonneg.mp
    convert hminus using 1; module

theorem operatorTraceNorm_positive_sandwich_difference_bound {A S T : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    {η : ℝ} (hη : 0 < η) :
    operatorTraceNorm (S * A * S - T * A * T) ≤
      ENNReal.ofReal ((1 + η⁻¹) * ‖S - T‖ ^ 2 + η * ‖T‖ ^ 2) * positiveTrace A := by
  obtain ⟨κ, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  let D := S - T
  have hD : IsSelfAdjoint D := hS.sub hT
  have hDD : 0 ≤ D * A * D := hD.conjugate_nonneg hA.1
  have hTT : 0 ≤ T * A * T := hT.conjugate_nonneg hA.1
  have hcA := positiveTraceClass_isCompactOperator hA
  have hc : IsCompactOperator (S * A * S - T * A * T) :=
    ((hcA.clm_comp S).comp_clm S).sub ((hcA.clm_comp T).comp_clm T)
  have hs : IsSelfAdjoint (S * A * S - T * A * T) :=
    (selfAdjoint_sandwich_isSelfAdjoint hA.1.isSelfAdjoint hS).sub
      (selfAdjoint_sandwich_isSelfAdjoint hA.1.isSelfAdjoint hT)
  have hcoef : 0 ≤ 1 + η⁻¹ := by positivity
  obtain ⟨hlo, hhi⟩ := positive_sandwich_difference_order hA.1 hS hT hη
  have hb := operatorTraceNorm_le_positiveTrace_of_order_bounds hc hs
    (add_nonneg (smul_nonneg hcoef hDD) (smul_nonneg hη.le hTT)) hlo hhi
  rw [positiveTrace_add (smul_nonneg hcoef hDD) (smul_nonneg hη.le hTT),
    positiveTrace_real_smul b hDD hcoef, positiveTrace_real_smul b hTT hη.le] at hb
  have hd : positiveTrace (D * A * D) ≤ ENNReal.ofReal (‖D‖ ^ 2) * positiveTrace A := by
    have h := positiveTrace_adjoint_sandwich_le hA.1 D
    change positiveTrace (D.adjoint * (A * D)) ≤ _ at h
    simpa only [hD.adjoint_eq, ← mul_assoc] using h
  have ht : positiveTrace (T * A * T) ≤ ENNReal.ofReal (‖T‖ ^ 2) * positiveTrace A := by
    have h := positiveTrace_adjoint_sandwich_le hA.1 T
    change positiveTrace (T.adjoint * (A * T)) ≤ _ at h
    simpa only [hT.adjoint_eq, ← mul_assoc] using h
  apply (hb.trans (add_le_add (_root_.mul_le_mul_right hd _)
    (_root_.mul_le_mul_right ht _))).trans_eq
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ← ENNReal.ofReal_mul hcoef,
    ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem operatorTraceNorm_positive_sandwich_difference_modulus {A S T : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    operatorTraceNorm (S * A * S - T * A * T) ≤
      ENNReal.ofReal (‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2)) * positiveTrace A := by
  by_cases hzero : S - T = 0
  · have he : S = T := sub_eq_zero.mp hzero
    subst S
    simp only [sub_self, operatorTraceNorm_of_nonneg (le_refl 0), positiveTrace_zero,
      norm_zero, zero_mul, ENNReal.ofReal_zero]
    exact le_rfl
  · have hn : 0 < ‖S - T‖ := norm_pos_iff.mpr hzero
    have h := operatorTraceNorm_positive_sandwich_difference_bound hA hS hT hn
    have he : (1 + ‖S - T‖⁻¹) * ‖S - T‖ ^ 2 + ‖S - T‖ * ‖T‖ ^ 2 =
        ‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2) := by
      field_simp
    rwa [he] at h

end VacuumBellSeparation.Gaussian
