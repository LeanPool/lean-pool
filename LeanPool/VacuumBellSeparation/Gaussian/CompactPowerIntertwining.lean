/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertEigenTrace

/-!
# Actual CFC intertwining and cyclic positive power traces

A bounded map intertwining positive operators also intertwines their
positive powers when the source operator is compact. This follows on its
actual Hilbert eigenbasis, with zero image vectors handled explicitly.
The Hilbert--Schmidt cyclic trace then identifies Tr((T†T)^q) and
Tr((TT†)^q) for q >= 1. No polar decomposition or bounded inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem positiveOperator_rpow_add_nonneg {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : A ^ (s + t) = A ^ s * A ^ t := by
  rw [CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hA,
    ← cfc_mul _ _ A (Real.continuous_rpow_const hs).continuousOn
      (Real.continuous_rpow_const ht).continuousOn]
  exact cfc_congr fun x hx => Real.rpow_add_of_nonneg
    (spectrum_nonneg_of_nonneg hA hx) hs ht

theorem compact_positive_rpow_intertwine {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hcA : IsCompactOperator A) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (S : E →L[ℂ] F) (hS : B.comp S = S.comp A) {p : ℝ} (hp : 0 < p) :
    (B ^ p).comp S = S.comp (A ^ p) := by
  let b := compactSelfAdjointBasis hcA hA.isSelfAdjoint
  have heig (i : operatorEigenIndex A) : A (b i) = i.1.re • b i := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcA hA.isSelfAdjoint i
  apply continuousLinearMap_eq_of_dense_span b b.dense_span
  intro i
  have hBi : B (S (b i)) = i.1.re • S (b i) := by
    have h := DFunLike.congr_fun hS (b i)
    simpa only [comp_apply, heig, map_smul_of_tower] using h
  rw [comp_apply, comp_apply, hilbertEigenbasis_rpow_apply b hA heig hp,
    map_smul_of_tower]
  by_cases hi : S (b i) = 0
  · simp only [hi, map_zero, smul_zero]
  · exact rpow_apply_eigenvector hB (eigenvalue_mem_real_spectrum hi hBi) hBi hp

theorem positiveTrace_star_mul_self_rpow (T : E →L[ℂ] E)
    (hc : IsCompactOperator (star T * T)) {q : ℝ} (hq : 1 ≤ q) :
    positiveTrace ((star T * T) ^ q) = positiveTrace ((T * star T) ^ q) := by
  let A := star T * T
  let B := T * star T
  have hA : 0 ≤ A := nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T)
  have hB : 0 ≤ B := nonneg_iff_isPositive.mpr (isPositive_self_comp_adjoint T)
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    rw [CFC.rpow_one _ hA, CFC.rpow_one _ hB]
    exact positiveTrace_adjoint_comp_eq_comp_adjoint T
  let s := (q - 1) / 2
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hp : 0 < q - 1 := sub_pos.mpr hq
  have hI := compact_positive_rpow_intertwine hc hA hB T
    (show B.comp T = T.comp A by
      change (T * star T) * T = T * (star T * T)
      exact mul_assoc _ _ _) hp
  change B ^ (q - 1) * T = T * A ^ (q - 1) at hI
  let S := T * A ^ s
  have hAs : star (A ^ s) = A ^ s := CFC.rpow_nonneg.isSelfAdjoint.star_eq
  have hSS : S.adjoint.comp S = A ^ q := by
    change star (T * A ^ s) * (T * A ^ s) = A ^ q
    rw [star_mul, hAs]
    calc
      _ = A ^ s * A * A ^ s := by dsimp only [A]; noncomm_ring
      _ = A ^ s * A ^ (1 : ℝ) * A ^ s := by rw [CFC.rpow_one A hA]
      _ = A ^ (s + 1) * A ^ s := by rw [positiveOperator_rpow_add_nonneg hA hs zero_le_one]
      _ = A ^ (s + 1 + s) := (positiveOperator_rpow_add_nonneg hA (by positivity) hs).symm
      _ = A ^ q := by congr 1; dsimp only [s]; ring
  have hSS' : S.comp S.adjoint = B ^ q := by
    change (T * A ^ s) * star (T * A ^ s) = B ^ q
    rw [star_mul, hAs]
    calc
      _ = T * (A ^ s * A ^ s) * star T := by noncomm_ring
      _ = T * A ^ (s + s) * star T := by rw [positiveOperator_rpow_add_nonneg hA hs hs]
      _ = T * A ^ (q - 1) * star T := by
        have hs' : s + s = q - 1 := by
          dsimp only [s]
          ring
        rw [hs']
      _ = B ^ (q - 1) * B := by rw [← hI, mul_assoc]
      _ = B ^ (q - 1) * B ^ (1 : ℝ) := by rw [CFC.rpow_one B hB]
      _ = B ^ (q - 1 + 1) := (positiveOperator_rpow_add_nonneg hB hp.le zero_le_one).symm
      _ = B ^ q := by rw [sub_add_cancel]
  rw [← hSS, ← hSS']
  exact positiveTrace_adjoint_comp_eq_comp_adjoint S

end VacuumBellSeparation.Gaussian
