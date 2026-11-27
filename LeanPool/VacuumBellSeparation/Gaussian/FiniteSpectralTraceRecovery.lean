/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteSignedTraceTests
public import LeanPool.VacuumBellSeparation.Gaussian.TraceNormCompression

/-!
# Finite spectral sign tests recover the genuine extended nuclear trace

The actual compact selfadjoint eigenbasis includes the kernel. Finite sign
projections recover finite absolute eigenvalue sums, and their supremum is
the full trace norm, without prior trace finiteness or separability.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Real spectral sign defined as `if 0 ≤ x then 1 else -1`. -/
def realSpectralSign (x : ℝ) : ℂ := if 0 ≤ x then 1 else -1

@[simp] theorem norm_realSpectralSign (x : ℝ) : ‖realSpectralSign x‖ = 1 := by
  unfold realSpectralSign
  split_ifs <;> simp

@[simp] theorem realSpectralSign_mul (x : ℝ) : realSpectralSign x * (x : ℂ) = ((|x| : ℝ) : ℂ) := by
  unfold realSpectralSign
  split_ifs with hx
  · rw [one_mul, abs_of_nonneg hx]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hx), Complex.ofReal_neg]

theorem finite_spectral_sign_trace {B : E →L[ℂ] E}
    (hc : IsCompactOperator B) (hB : IsSelfAdjoint B) (s : Finset (operatorEigenIndex B)) :
    finiteTraceTest (compactSelfAdjointBasis hc hB) s
      (fun i => realSpectralSign i.1.re) B = ((∑ i ∈ s, |i.1.re| : ℝ) : ℂ) := by
  rw [finiteTraceTest_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [compactSelfAdjointBasis_apply_operator, inner_smul_right,
    inner_self_eq_norm_sq_to_K, (compactSelfAdjointBasis hc hB).orthonormal.norm_eq_one]
  simp only [one_pow, RCLike.ofReal_one, mul_one, realSpectralSign_mul]

theorem operatorTraceNorm_le_of_finite_tests {B : E →L[ℂ] E}
    (hc : IsCompactOperator B) (hB : IsSelfAdjoint B) {C : ℝ}
    (h : ∀ s : Finset (operatorEigenIndex B),
      ‖finiteTraceTest (compactSelfAdjointBasis hc hB) s
        (fun i => realSpectralSign i.1.re) B‖ ≤ C) :
    operatorTraceNorm B ≤ ENNReal.ofReal C := by
  classical
  rw [operatorTraceNorm_eq_eigenvalue_sum hc hB, tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg i.1.re)]
  apply ENNReal.ofReal_le_ofReal
  have hs := h s
  rw [finite_spectral_sign_trace, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hs
  exact hs

theorem norm_finiteTraceTest_unitary_sandwich_le (b : HilbertBasis κ ℂ E)
    {u : ι → E} (hu : Orthonormal ℂ u) (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞)
    (U : unitary (E →L[ℂ] E)) :
    ‖finiteTraceTest u s w ((U : E →L[ℂ] E) * B * U)‖ ≤ (operatorTraceNorm B).toReal := by
  rw [finiteTraceTest_two_sided b u s w hB ht]
  apply (norm_jordanExpectation_le b hB ht _).trans
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_finiteTraceTestOperator_le_one hu s w hw) ENNReal.toReal_nonneg

theorem selfAdjoint_sandwich_isSelfAdjoint {B S : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (hS : IsSelfAdjoint S) : IsSelfAdjoint (S * B * S) := by
  simpa only [hS.adjoint_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    using hB.adjoint_conj S

theorem operatorTraceNorm_selfAdjoint_sandwich_le {B S : E →L[ℂ] E}
    (hc : IsCompactOperator B) (hB : IsSelfAdjoint B) (hS : IsSelfAdjoint S) :
    operatorTraceNorm (S * B * S) ≤ ENNReal.ofReal (‖S‖ ^ 2) * operatorTraceNorm B := by
  simpa only [hS.adjoint_eq, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    using operatorTraceNorm_adjoint_sandwich_le hc hB S

theorem operatorTraceNorm_selfAdjoint_sandwich_lt_top {B S : E →L[ℂ] E}
    (hc : IsCompactOperator B) (hB : IsSelfAdjoint B)
    (ht : operatorTraceNorm B < ∞) (hS : IsSelfAdjoint S) :
    operatorTraceNorm (S * B * S) < ∞ :=
  (operatorTraceNorm_selfAdjoint_sandwich_le hc hB hS).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ht)

end VacuumBellSeparation.Gaussian
