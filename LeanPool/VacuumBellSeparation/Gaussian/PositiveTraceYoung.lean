/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertEigenTrace

/-!
# Young's trace inequality for actual compact positive operators

Apply scalar Young to the actual two-eigenbasis overlap formula. Parseval
makes both overlap marginals one. All sums are extended nonnegative sums,
so the result retains infinite power traces without a summability premise.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal ContinuousFunctionalCalculus

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem hilbertOverlap_young (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {a : ι → ℝ} {d : κ → ℝ} (ha : ∀ i, 0 ≤ a i) (hd : ∀ j, 0 ≤ d j)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∑' i, ∑' j, ENNReal.ofReal (a i) * ENNReal.ofReal (d j) *
      hilbertBasisOverlap b c i j) ≤
      (∑' i, ENNReal.ofReal (a i ^ p)) / ENNReal.ofReal p +
      (∑' j, ENNReal.ofReal (d j ^ q)) / ENNReal.ofReal q := by
  have hterm (i : ι) (j : κ) :
      ENNReal.ofReal (a i) * ENNReal.ofReal (d j) ≤
        ENNReal.ofReal (a i ^ p) / ENNReal.ofReal p +
        ENNReal.ofReal (d j ^ q) / ENNReal.ofReal q := by
    have h := ENNReal.ofReal_le_ofReal (Real.young_inequality_of_nonneg (ha i) (hd j) hpq)
    simpa only [ENNReal.ofReal_mul (ha i),
      ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg (ha i) p) hpq.nonneg)
        (div_nonneg (Real.rpow_nonneg (hd j) q) hpq.symm.nonneg),
      ENNReal.ofReal_div_of_pos hpq.pos, ENNReal.ofReal_div_of_pos hpq.symm.pos] using h
  have hleft : (∑' i, ∑' j,
      (ENNReal.ofReal (a i ^ p) / ENNReal.ofReal p) * hilbertBasisOverlap b c i j) =
      (∑' i, ENNReal.ofReal (a i ^ p)) / ENNReal.ofReal p := by
    simp only [ENNReal.tsum_mul_left, hilbertBasisOverlap_tsum_right, mul_one,
      div_eq_mul_inv, ENNReal.tsum_mul_right]
  have hright : (∑' i, ∑' j,
      (ENNReal.ofReal (d j ^ q) / ENNReal.ofReal q) * hilbertBasisOverlap b c i j) =
      (∑' j, ENNReal.ofReal (d j ^ q)) / ENNReal.ofReal q := by
    rw [tsum_comm]
    simp only [ENNReal.tsum_mul_left, hilbertBasisOverlap_tsum_left, mul_one,
      div_eq_mul_inv, ENNReal.tsum_mul_right]
  calc
    _ ≤ ∑' i, ∑' j,
        (ENNReal.ofReal (a i ^ p) / ENNReal.ofReal p +
          ENNReal.ofReal (d j ^ q) / ENNReal.ofReal q) * hilbertBasisOverlap b c i j := by
      exact tsum_le_tsum fun i => tsum_le_tsum fun j =>
        _root_.mul_le_mul_left (hterm i j) _
    _ = _ := by
      simp_rw [add_mul, tsum_add]
      rw [hleft, hright]

theorem positiveTrace_sandwich_young_of_eigenbases
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {a : ι → ℝ} {d : κ → ℝ} (ha₀ : ∀ i, 0 ≤ a i) (hd₀ : ∀ j, 0 ≤ d j)
    (ha : ∀ i, A (b i) = a i • b i) (hd : ∀ j, B (c j) = d j • c j)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    positiveTrace (CFC.sqrt B * A * CFC.sqrt B) ≤
      positiveTrace (A ^ p) / ENNReal.ofReal p + positiveTrace (B ^ q) / ENNReal.ofReal q := by
  rw [positiveTrace_sandwich_eq_hilbertEigenvalue_overlap b c hA hB ha₀ hd₀ ha hd,
    positiveTrace_rpow_eq_hilbertEigenvalue_sum b hA ha hpq.pos,
    positiveTrace_rpow_eq_hilbertEigenvalue_sum c hB hd hpq.symm.pos]
  exact hilbertOverlap_young b c ha₀ hd₀ hpq

theorem positiveTrace_sandwich_young {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    positiveTrace (CFC.sqrt B * A * CFC.sqrt B) ≤
      positiveTrace (A ^ p) / ENNReal.ofReal p + positiveTrace (B ^ q) / ENNReal.ofReal q := by
  let b := compactSelfAdjointBasis hcA hA.isSelfAdjoint
  let c := compactSelfAdjointBasis hcB hB.isSelfAdjoint
  apply positiveTrace_sandwich_young_of_eigenbases b c hA hB
    (operatorEigenFamily_eigenvalue_nonneg hA) (operatorEigenFamily_eigenvalue_nonneg hB)
    _ _ hpq
  · intro i
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcA hA.isSelfAdjoint i
  · intro j
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using
      compactSelfAdjointBasis_apply_operator hcB hB.isSelfAdjoint j

end VacuumBellSeparation.Gaussian
