/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTracePowerOrder
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtIdeal

/-!
# Actual trace-power bounds under Hilbert-space compression

Unit-vector Jensen and a genuine eigenbasis of the compact compressed
operator give Tr((i† A i)^p) <= Tr(i† A^p i), p>=1. The Hilbert--Schmidt
ideal bound and the actual isometry norm then give Tr(i† A^p i)<=Tr(A^p).
No operator convexity at p>2 or finite-dimensional trace substitute occurs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem compression_inner (ι : E →ₗᵢ[ℂ] F) (A : F →L[ℂ] F) (x y : E) :
    inner ℂ x (compression ι A y) = inner ℂ (ι x) (A (ι y)) := by
  change inner ℂ x (ι.toContinuousLinearMap.adjoint (A (ι y))) = _
  exact ι.toContinuousLinearMap.adjoint_inner_right x (A (ι y))

theorem positiveTrace_compression_le (ι : E →ₗᵢ[ℂ] F) {A : F →L[ℂ] F}
    (hA : 0 ≤ A) : positiveTrace (compression ι A) ≤ positiveTrace A := by
  have hn : ‖ι.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [LinearIsometry.coe_toContinuousLinearMap, ι.norm_map, one_mul, le_refl]
  have hn₂ : ‖ι.toContinuousLinearMap‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg ι.toContinuousLinearMap]
  have he : ENNReal.ofReal (‖ι.toContinuousLinearMap‖ ^ 2) ≤ 1 :=
    (ENNReal.ofReal_le_ofReal hn₂).trans_eq (by norm_num)
  have h := positiveTrace_adjoint_sandwich_le hA ι.toContinuousLinearMap
  have hh : positiveTrace (compression ι A) ≤
      ENNReal.ofReal (‖ι.toContinuousLinearMap‖ ^ 2) * positiveTrace A := by
    simpa only [compression, comp_assoc] using h
  exact hh.trans (by simpa only [one_mul] using _root_.mul_le_mul_left he (positiveTrace A))

theorem unit_inner_pow_le_inner_rpow {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {x : E} (hx : ‖x‖ = 1) {p : ℝ} (hp : 1 ≤ p) :
    (inner ℂ x (A x)).re ^ p ≤ (inner ℂ x ((A ^ p) x)).re := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hj := unit_inner_rpow_le (CFC.rpow_nonneg (a := A) (y := p)) hx
    (one_div_pos.mpr hp₀) ((div_le_iff₀ hp₀).mpr (by simpa using hp))
  rw [CFC.rpow_rpow_of_exponent_nonneg A p (1 / p) hp₀.le (one_div_pos.mpr hp₀).le hA,
    mul_one_div_cancel hp₀.ne', CFC.rpow_one A hA] at hj
  have hbase : 0 ≤ (inner ℂ x (A x)).re :=
    (nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _
  have htarget : 0 ≤ (inner ℂ x ((A ^ p) x)).re :=
    (nonneg_iff_isPositive.mp (CFC.rpow_nonneg (a := A) (y := p))).re_inner_nonneg_right _
  have hh := Real.rpow_le_rpow hbase hj hp₀.le
  rwa [← Real.rpow_mul htarget, one_div_mul_cancel hp₀.ne', Real.rpow_one] at hh

theorem positiveTrace_compression_rpow_le_compression (ι : E →ₗᵢ[ℂ] F)
    {A : F →L[ℂ] F} (hc : IsCompactOperator (compression ι A)) (hA : 0 ≤ A)
    {p : ℝ} (hp : 1 ≤ p) :
    positiveTrace (compression ι A ^ p) ≤ positiveTrace (compression ι (A ^ p)) := by
  let C := compression ι A
  have hC : 0 ≤ C := compression_nonneg ι hA
  let b := compactSelfAdjointBasis hc hC.isSelfAdjoint
  have heig (i : operatorEigenIndex C) : C (b i) = i.1.re • b i := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hc hC.isSelfAdjoint i
  have hdiag (i : operatorEigenIndex C) : (inner ℂ (ι (b i)) (A (ι (b i)))).re = i.1.re := by
    rw [← compression_inner ι A]
    change RCLike.re (inner ℂ (b i) (C (b i))) = _
    rw [heig, inner_smul_right_eq_smul, RCLike.smul_re, inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one]
    simp
  rw [positiveTrace_rpow_eq_hilbertEigenvalue_sum b hC heig (lt_of_lt_of_le zero_lt_one hp),
    positiveTrace_eq_tsum_diagonal b (compression_nonneg ι (CFC.rpow_nonneg (a := A) (y := p)))]
  apply tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  rw [compression_inner]
  have h := unit_inner_pow_le_inner_rpow hA
    (show ‖ι (b i)‖ = 1 by rw [ι.norm_map, b.orthonormal.norm_eq_one]) hp
  rwa [hdiag] at h

theorem positiveTrace_compression_rpow_le (ι : E →ₗᵢ[ℂ] F)
    {A : F →L[ℂ] F} (hcA : IsCompactOperator A) (hA : 0 ≤ A)
    {p : ℝ} (hp : 1 ≤ p) :
    positiveTrace (compression ι A ^ p) ≤ positiveTrace (A ^ p) := by
  have hc : IsCompactOperator (compression ι A) :=
    (hcA.comp_clm ι.toContinuousLinearMap).clm_comp ι.toContinuousLinearMap.adjoint
  exact (positiveTrace_compression_rpow_le_compression ι hc hA hp).trans
    (positiveTrace_compression_le ι (CFC.rpow_nonneg (a := A) (y := p)))

end VacuumBellSeparation.Gaussian
