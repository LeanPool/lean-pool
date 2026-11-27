/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceYoung
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder's inequality for the actual positive sandwich trace

The counting-measure form of the pinned extended-valued Hölder inequality
applies to arbitrary index sets. Insert the actual doubly stochastic
Hilbert-basis overlap weights to obtain positive Schatten Hölder for
compact positive operators, including zero and infinite power traces.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ENNReal ContinuousFunctionalCalculus

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem ennreal_tsum_holder (f g : ι → ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∑' i, f i * g i) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  let : MeasurableSpace ι := ⊤
  have hf : Measurable f := measurable_from_top
  have hg : Measurable g := measurable_from_top
  simpa only [Pi.mul_apply, lintegral_count] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count hpq hf.aemeasurable hg.aemeasurable

omit [CompleteSpace E] in
theorem hilbertOverlap_holder (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (a : ι → ℝ≥0∞) (d : κ → ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∑' i, ∑' j, a i * d j * hilbertBasisOverlap b c i j) ≤
      (∑' i, a i ^ p) ^ (1 / p) * (∑' j, d j ^ q) ^ (1 / q) := by
  let f : ι × κ → ℝ≥0∞ := fun ij => a ij.1 * hilbertBasisOverlap b c ij.1 ij.2 ^ (1 / p)
  let g : ι × κ → ℝ≥0∞ := fun ij => d ij.2 * hilbertBasisOverlap b c ij.1 ij.2 ^ (1 / q)
  have hf (i : ι) (j : κ) : f (i, j) ^ p = a i ^ p * hilbertBasisOverlap b c i j := by
    dsimp only [f]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpq.ne_zero, ENNReal.rpow_one]
  have hg (i : ι) (j : κ) : g (i, j) ^ q = d j ^ q * hilbertBasisOverlap b c i j := by
    dsimp only [g]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpq.symm.ne_zero, ENNReal.rpow_one]
  have hfg (i : ι) (j : κ) : f (i, j) * g (i, j) =
      a i * d j * hilbertBasisOverlap b c i j := by
    dsimp only [f, g]
    calc
      _ = (a i * d j) * (hilbertBasisOverlap b c i j ^ (1 / p) *
          hilbertBasisOverlap b c i j ^ (1 / q)) := by ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg,
          one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
  have hfsum : (∑' ij, f ij ^ p) = ∑' i, a i ^ p := by
    rw [tsum_prod']
    simp only [hf, ENNReal.tsum_mul_left, hilbertBasisOverlap_tsum_right, mul_one]
  have hgsum : (∑' ij, g ij ^ q) = ∑' j, d j ^ q := by
    rw [tsum_prod', tsum_comm]
    simp only [hg, ENNReal.tsum_mul_left, hilbertBasisOverlap_tsum_left, mul_one]
  have h := ennreal_tsum_holder f g hpq
  rw [hfsum, hgsum, tsum_prod'] at h
  simpa only [hfg] using h

theorem positiveTrace_sandwich_holder_of_eigenbases
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {a : ι → ℝ} {d : κ → ℝ} (ha₀ : ∀ i, 0 ≤ a i) (hd₀ : ∀ j, 0 ≤ d j)
    (ha : ∀ i, A (b i) = a i • b i) (hd : ∀ j, B (c j) = d j • c j)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    positiveTrace (CFC.sqrt B * A * CFC.sqrt B) ≤
      positiveTrace (A ^ p) ^ (1 / p) * positiveTrace (B ^ q) ^ (1 / q) := by
  rw [positiveTrace_sandwich_eq_hilbertEigenvalue_overlap b c hA hB ha₀ hd₀ ha hd,
    positiveTrace_rpow_eq_hilbertEigenvalue_sum b hA ha hpq.pos,
    positiveTrace_rpow_eq_hilbertEigenvalue_sum c hB hd hpq.symm.pos]
  simpa only [← ENNReal.ofReal_rpow_of_nonneg (ha₀ _) hpq.nonneg,
    ← ENNReal.ofReal_rpow_of_nonneg (hd₀ _) hpq.symm.nonneg] using
    hilbertOverlap_holder b c (fun i => ENNReal.ofReal (a i))
      (fun j => ENNReal.ofReal (d j)) hpq

theorem positiveTrace_sandwich_holder {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    positiveTrace (CFC.sqrt B * A * CFC.sqrt B) ≤
      positiveTrace (A ^ p) ^ (1 / p) * positiveTrace (B ^ q) ^ (1 / q) := by
  let b := compactSelfAdjointBasis hcA hA.isSelfAdjoint
  let c := compactSelfAdjointBasis hcB hB.isSelfAdjoint
  apply positiveTrace_sandwich_holder_of_eigenbases b c hA hB
    (operatorEigenFamily_eigenvalue_nonneg hA) (operatorEigenFamily_eigenvalue_nonneg hB)
    _ _ hpq
  · intro i
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcA hA.isSelfAdjoint i
  · intro j
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcB hB.isSelfAdjoint j

end VacuumBellSeparation.Gaussian
