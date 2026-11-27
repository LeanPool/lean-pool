/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactPositivePowers
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceHolder
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The actual extended trace norm and self-adjoint order bounds

This is the trace of the genuine operator absolute value on the full
Hilbert space. Compact self-adjoint operators have an actual Hilbert
eigenbasis, which identifies this trace with the extended absolute
eigenvalue sum. The order estimate uses diagonal quadratic forms and
never asserts the false implication `-B ≤ A ≤ B → |A| ≤ B`.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The genuine extended Schatten one norm, allowed to be infinite. -/
def operatorTraceNorm (A : E →L[ℂ] E) : ℝ≥0∞ := positiveTrace (CFC.abs A)

theorem isCompactOperator_abs {A : E →L[ℂ] E} (hc : IsCompactOperator A)
    (hA : IsSelfAdjoint A) : IsCompactOperator (CFC.abs A : E →L[ℂ] E) := by
  have he : CFC.abs A = cfcₙ (A := E →L[ℂ] E) (fun x : ℝ => ‖x‖) A :=
    CFC.abs_eq_cfcₙ_norm A hA
  rw [he]
  exact isCompactOperator_cfcₙ hc hA (fun x : ℝ => ‖x‖)
    continuous_norm.continuousOn (norm_zero : ‖(0 : ℝ)‖ = 0)

theorem operatorTraceNorm_eq_eigenvalue_sum {A : E →L[ℂ] E}
    (hc : IsCompactOperator A) (hA : IsSelfAdjoint A) :
    operatorTraceNorm A = ∑' i : operatorEigenIndex A, ENNReal.ofReal |i.1.re| := by
  let b := compactSelfAdjointBasis hc hA
  have heig (i : operatorEigenIndex A) : A (b i) = i.1.re • b i := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hc hA i
  have habs (i : operatorEigenIndex A) : CFC.abs A (b i) = |i.1.re| • b i := by
    have hn : b i ≠ 0 := by
      intro h
      simpa [h] using b.orthonormal.norm_eq_one i
    rw [CFC.abs_eq_cfc_norm A hA]
    simpa only [Real.norm_eq_abs] using cfc_apply_eigenvector hA
      (eigenvalue_mem_real_spectrum hn (heig i)) (heig i) (fun x : ℝ => ‖x‖)
      continuous_norm.continuousOn
  rw [operatorTraceNorm, positiveTrace_eq_tsum_diagonal b (CFC.abs_nonneg A)]
  apply tsum_congr
  intro i
  change ENNReal.ofReal (RCLike.re (inner ℂ (b i) (CFC.abs A (b i)))) = _
  rw [habs, inner_smul_right_eq_smul, RCLike.smul_re, inner_self_eq_norm_sq,
    b.orthonormal.norm_eq_one]
  simp

theorem operator_abs_sub_nonneg {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    0 ≤ CFC.abs A - A := by
  rw [CFC.abs_sub_self A hA, two_smul]
  exact add_nonneg (CFC.negPart_nonneg A) (CFC.negPart_nonneg A)

theorem operator_abs_add_nonneg {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    0 ≤ CFC.abs A + A := by
  rw [CFC.abs_add_self A hA, two_smul]
  exact add_nonneg (CFC.posPart_nonneg A) (CFC.posPart_nonneg A)

theorem operatorTraceNorm_le_positiveTrace_of_order_bounds
    {A B : E →L[ℂ] E} (hc : IsCompactOperator A) (hA : IsSelfAdjoint A)
    (hB : 0 ≤ B) (hlo : -B ≤ A) (hhi : A ≤ B) :
    operatorTraceNorm A ≤ positiveTrace B := by
  let b := compactSelfAdjointBasis hc hA
  have heig (i : operatorEigenIndex A) : (inner ℂ (b i) (A (b i))).re = i.1.re := by
    rw [compactSelfAdjointBasis_apply_operator, inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one]
    simp only [one_pow, RCLike.ofReal_one, mul_one, Complex.ofReal_re]
  rw [operatorTraceNorm_eq_eigenvalue_sum hc hA, positiveTrace_eq_tsum_diagonal b hB]
  apply tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr hhi)).re_inner_nonneg_right (b i)
  have hl := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (neg_le_iff_add_nonneg'.mp hlo)).re_inner_nonneg_right (b i)
  simp only [sub_apply, add_apply, inner_sub_right, inner_add_right,
    RCLike.re_eq_complex_re, Complex.sub_re, Complex.add_re, heig] at hh hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem operatorTraceNorm_add_le {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    operatorTraceNorm (A + B) ≤ operatorTraceNorm A + operatorTraceNorm B := by
  have hu := add_le_add (sub_nonneg.mp (operator_abs_sub_nonneg hA))
    (sub_nonneg.mp (operator_abs_sub_nonneg hB))
  have hl : -(CFC.abs A + CFC.abs B) ≤ A + B := by
    simpa only [neg_add] using add_le_add
      (neg_le_iff_add_nonneg'.mpr (operator_abs_add_nonneg hA))
      (neg_le_iff_add_nonneg'.mpr (operator_abs_add_nonneg hB))
  have h := operatorTraceNorm_le_positiveTrace_of_order_bounds (hcA.add hcB) (hA.add hB)
    (add_nonneg (CFC.abs_nonneg A) (CFC.abs_nonneg B)) hl hu
  simpa only [positiveTrace_add (CFC.abs_nonneg A) (CFC.abs_nonneg B), operatorTraceNorm] using h

@[simp] theorem operatorTraceNorm_of_nonneg {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    operatorTraceNorm A = positiveTrace A := by
  rw [operatorTraceNorm, CFC.abs_of_nonneg A hA]

@[simp] theorem operatorTraceNorm_neg (A : E →L[ℂ] E) :
    operatorTraceNorm (-A) = operatorTraceNorm A := by simp only [operatorTraceNorm, CFC.abs_neg]

theorem operatorTraceNorm_sub_le {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    operatorTraceNorm (A - B) ≤ operatorTraceNorm A + operatorTraceNorm B := by
  simpa only [sub_eq_add_neg, operatorTraceNorm_neg] using
    operatorTraceNorm_add_le hcA hcB.neg hA hB.neg

theorem operatorTraceNorm_density_difference_lt_top {ρ σ : E →L[ℂ] E}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ) :
    operatorTraceNorm (ρ - σ) < ∞ := by
  exact (operatorTraceNorm_sub_le (positiveTraceClass_isCompactOperator hρ)
    (positiveTraceClass_isCompactOperator hσ) hρ.1.isSelfAdjoint hσ.1.isSelfAdjoint).trans_lt
      (by simpa only [operatorTraceNorm_of_nonneg hρ.1, operatorTraceNorm_of_nonneg hσ.1]
        using ENNReal.add_lt_top.mpr ⟨hρ.2, hσ.2⟩)

end VacuumBellSeparation.Gaussian
