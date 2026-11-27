/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceHolder
public import LeanPool.VacuumBellSeparation.Gaussian.ContractionDilation

/-!
# Scalar compression Jensen and monotonicity of positive power traces

One-dimensional compression gives the unit-vector concavity inequality.
Applying it to B^q with exponent 1/q compares every eigenvalue power of
A <= B with a diagonal entry of B^q. The actual extended trace is therefore
monotone for q >= 1 when A is compact. B need not be compact or trace class.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ComplexOrder ContinuousFunctionalCalculus

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem compression_unitVector_apply {x : E} (hx : ‖x‖ = 1)
    (A : E →L[ℂ] E) (z : ℂ) :
    compression (LinearIsometry.toSpanSingleton ℂ E hx) A z = z * inner ℂ x (A x) := by
  change (toSpanSingleton ℂ x).adjoint (A (z • x)) = _
  rw [adjoint_toSpanSingleton, innerSL_apply_apply, map_smul, inner_smul_right]

theorem unit_inner_rpow_le {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {x : E} (hx : ‖x‖ = 1) {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    (inner ℂ x ((A ^ p) x)).re ≤ (inner ℂ x (A x)).re ^ p := by
  let v := LinearIsometry.toSpanSingleton ℂ E hx
  let a := (inner ℂ x (A x)).re
  have hreal : (a : ℂ) = inner ℂ x (A x) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp
        ((nonneg_iff_isPositive.mp hA).inner_nonneg_right x)).2
  have heig : compression v A (1 : ℂ) = a • (1 : ℂ) := by
    rw [compression_unitVector_apply, one_mul, ← hreal]
    simp only [Complex.real_smul, mul_one]
  have hpow := rpow_apply_eigenvector (compression_nonneg v hA)
    (eigenvalue_mem_real_spectrum one_ne_zero heig) heig hp₀
  have hj := (nonneg_iff_isPositive.mp
    (sub_nonneg.mpr (compression_rpow_le v hA hp₀ hp₁))).re_inner_nonneg_right (1 : ℂ)
  have hdiag₁ : (inner ℂ (1 : ℂ) (compression v (A ^ p) 1)).re =
      (inner ℂ x ((A ^ p) x)).re := by
    rw [compression_unitVector_apply]
    simp only [one_mul, RCLike.inner_apply', map_one]
  have hdiag₂ : (inner ℂ (1 : ℂ) ((compression v A ^ p) 1)).re = a ^ p := by
    rw [hpow]
    simp only [RCLike.inner_apply', map_one, one_mul, Complex.real_smul, mul_one,
      Complex.ofReal_re]
  simp only [sub_apply, inner_sub_right, RCLike.re_eq_complex_re, Complex.sub_re,
    hdiag₁, hdiag₂] at hj
  exact sub_nonneg.mp hj

theorem positiveTrace_rpow_mono_of_eigenbasis (b : HilbertBasis ι ℂ E)
    {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hAB : A ≤ B)
    {a : ι → ℝ} (ha₀ : ∀ i, 0 ≤ a i) (ha : ∀ i, A (b i) = a i • b i)
    {q : ℝ} (hq : 1 ≤ q) : positiveTrace (A ^ q) ≤ positiveTrace (B ^ q) := by
  have hq₀ : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hB : 0 ≤ B := hA.trans hAB
  have hroot : (B ^ q) ^ (1 / q : ℝ) = B := by
    rw [CFC.rpow_rpow_of_exponent_nonneg B q (1 / q) hq₀.le
      (one_div_pos.mpr hq₀).le hB, mul_one_div_cancel hq₀.ne', CFC.rpow_one B hB]
  rw [positiveTrace_rpow_eq_hilbertEigenvalue_sum b hA ha hq₀,
    positiveTrace_eq_tsum_diagonal b (CFC.rpow_nonneg (a := B) (y := q))]
  apply tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  have hdiag : a i ≤ (inner ℂ (b i) (B (b i))).re := by
    have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hAB)).re_inner_nonneg_right (b i)
    rw [sub_apply, inner_sub_right, RCLike.re_eq_complex_re, Complex.sub_re, ha,
      inner_smul_right_eq_smul, ← RCLike.re_eq_complex_re, RCLike.smul_re,
      inner_self_eq_norm_sq, b.orthonormal.norm_eq_one] at h
    simpa only [one_pow, mul_one, RCLike.re_eq_complex_re] using sub_nonneg.mp h
  have hj := unit_inner_rpow_le (CFC.rpow_nonneg (a := B) (y := q))
    (b.orthonormal.norm_eq_one i) (one_div_pos.mpr hq₀)
    ((div_le_iff₀ hq₀).mpr (by simpa using hq))
  rw [hroot] at hj
  have h := Real.rpow_le_rpow (ha₀ i) (hdiag.trans hj) hq₀.le
  have hn : 0 ≤ (inner ℂ (b i) ((B ^ q) (b i))).re :=
    (nonneg_iff_isPositive.mp (CFC.rpow_nonneg (a := B) (y := q))).re_inner_nonneg_right _
  rwa [← Real.rpow_mul hn, one_div_mul_cancel hq₀.ne', Real.rpow_one] at h

theorem positiveTrace_rpow_mono {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hA : 0 ≤ A) (hAB : A ≤ B) {q : ℝ} (hq : 1 ≤ q) :
    positiveTrace (A ^ q) ≤ positiveTrace (B ^ q) := by
  apply positiveTrace_rpow_mono_of_eigenbasis (compactSelfAdjointBasis hcA hA.isSelfAdjoint)
    hA hAB (operatorEigenFamily_eigenvalue_nonneg hA) _ hq
  intro i
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
    compactSelfAdjointBasis_apply_operator hcA hA.isSelfAdjoint i

end VacuumBellSeparation.Gaussian
