/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace

/-!
# Order and faithfulness of the extended positive trace

These are consequences of the actual basis-independent diagonal trace,
including at infinite trace. In particular a positive operator has trace
zero only when the operator itself is zero.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem positiveTrace_zero : positiveTrace (0 : E →L[ℂ] E) = 0 := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  rw [positiveTrace_eq_tsum_diagonal b (le_refl 0)]
  simp

theorem positiveTrace_mono {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hAB : A ≤ B) :
    positiveTrace A ≤ positiveTrace B := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  have hB : 0 ≤ B := hA.trans hAB
  rw [positiveTrace_eq_tsum_diagonal b hA, positiveTrace_eq_tsum_diagonal b hB]
  apply tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  have hdiff := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr hAB)).re_inner_nonneg_right (b i)
  simp only [sub_apply, inner_sub_right, RCLike.re_eq_complex_re, Complex.sub_re] at hdiff
  linarith

theorem positiveTrace_add {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    positiveTrace (A + B) = positiveTrace A + positiveTrace B := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
  rw [positiveTrace_eq_tsum_diagonal b (add_nonneg hA hB),
    positiveTrace_eq_tsum_diagonal b hA, positiveTrace_eq_tsum_diagonal b hB,
    ← tsum_add]
  apply tsum_congr
  intro i
  have hAi : 0 ≤ (inner ℂ (b i) (A (b i))).re := by
    simpa only [RCLike.re_eq_complex_re] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right (b i)
  have hBi : 0 ≤ (inner ℂ (b i) (B (b i))).re := by
    simpa only [RCLike.re_eq_complex_re] using
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hB).re_inner_nonneg_right (b i)
  rw [add_apply, inner_add_right, Complex.add_re, ENNReal.ofReal_add hAi hBi]

theorem positiveTrace_eq_zero_iff {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    positiveTrace A = 0 ↔ A = 0 := by
  constructor
  · intro ht
    obtain ⟨s, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := E)
    rw [positiveTrace_eq_basisSquareTrace b] at ht
    change (∑' i, ENNReal.ofReal (‖CFC.sqrt A (b i)‖ ^ 2)) = 0 at ht
    have hterm := tsum_eq_zero_iff.mp ht
    have hb (i : s) : CFC.sqrt A (b i) = 0 := by
      apply norm_eq_zero.mp
      have hle : ‖CFC.sqrt A (b i)‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp (hterm i)
      nlinarith [norm_nonneg (CFC.sqrt A (b i))]
    have hs : CFC.sqrt A = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have hsum := (b.hasSum_repr x).mapL (CFC.sqrt A)
      have hzero : HasSum (fun _ : s => (0 : E)) (CFC.sqrt A x) := by
        simpa only [map_smul, hb, smul_zero] using hsum
      exact hzero.unique hasSum_zero
    calc
      A = (CFC.sqrt A) ^ 2 := (CFC.sq_sqrt A hA).symm
      _ = 0 := by rw [hs]; simp
  · rintro rfl
    exact positiveTrace_zero

theorem IsPositiveTraceClass.of_le {A B : E →L[ℂ] E}
    (hB : IsPositiveTraceClass B) (hA : 0 ≤ A) (hAB : A ≤ B) :
    IsPositiveTraceClass A :=
  ⟨hA, (positiveTrace_mono hA hAB).trans_lt hB.2⟩

theorem IsPositiveTraceClass.add {A B : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B) :
    IsPositiveTraceClass (A + B) := by
  refine ⟨add_nonneg hA.1 hB.1, ?_⟩
  rw [positiveTrace_add hA.1 hB.1]
  exact ENNReal.add_lt_top.mpr ⟨hA.2, hB.2⟩

end VacuumBellSeparation.Gaussian
