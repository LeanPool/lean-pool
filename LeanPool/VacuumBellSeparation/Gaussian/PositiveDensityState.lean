/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FamilyExpectation
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwichCriterion

/-!
# Complex expectations of an arbitrary actual positive trace-class density

For an actual positive trace-class operator A, the square-root family
`sqrt(A)e_i` defines an absolutely convergent complex expectation on every
bounded operator. Positive inputs agree with the actual positive trace of
the square-root sandwich. Trace-one operators give actual bundled states.
The Hilbert basis is explicit; basis independence is a separate theorem.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem summable_sqrt_basis_norm_sq (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    Summable fun i => ‖CFC.sqrt A (b i)‖ ^ 2 := by
  simpa only [sqrt_norm_sq_eq_diagonal hA.1] using hA.summable_diagonal b

theorem tsum_sqrt_basis_norm_sq (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) :
    (∑' i, ‖CFC.sqrt A (b i)‖ ^ 2) = (positiveTrace A).toReal := by
  have hn (i : ι) : 0 ≤ (inner ℂ (b i) (A (b i))).re :=
    (nonneg_iff_isPositive.mp hA.1).re_inner_nonneg_right _
  rw [positiveTrace_eq_tsum_diagonal b hA.1,
    ← ENNReal.ofReal_tsum_of_nonneg hn (hA.summable_diagonal b),
    ENNReal.toReal_ofReal (tsum_nonneg hn)]
  exact tsum_congr fun i => sqrt_norm_sq_eq_diagonal hA.1 (b i)

/-- Density expectation given by `familyExpectation (fun i => CFC.sqrt A (b i)) B`. -/
def densityExpectation (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E) : ℂ :=
  familyExpectation (fun i => CFC.sqrt A (b i)) B

/-- Density expectation continuous linear map of type `(E →L[ℂ] E) →L[ℂ] ℂ`. -/
def densityExpectationCLM (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  familyExpectationCLM _ (summable_sqrt_basis_norm_sq b hA)

theorem norm_densityExpectation_le (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) (B : E →L[ℂ] E) :
    ‖densityExpectation b A B‖ ≤ (positiveTrace A).toReal * ‖B‖ := by
  simpa only [densityExpectation, tsum_sqrt_basis_norm_sq b hA] using
    norm_familyExpectation_le _ (summable_sqrt_basis_norm_sq b hA) B

theorem densityExpectation_one (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) : densityExpectation b A 1 = ((positiveTrace A).toReal : ℂ) := by
  rw [densityExpectation, familyExpectation_one, tsum_sqrt_basis_norm_sq b hA]

theorem densityExpectation_nonneg (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E)
    {B : E →L[ℂ] E} (hB : 0 ≤ B) : 0 ≤ densityExpectation b A B :=
  familyExpectation_nonneg _ hB

theorem positiveTrace_density_sandwich (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : IsPositiveTraceClass A) {B : E →L[ℂ] E} (hB : 0 ≤ B) :
    positiveTrace (CFC.sqrt A * B * CFC.sqrt A) = ENNReal.ofReal (densityExpectation b A B).re := by
  let S := CFC.sqrt A
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hdiag (i : ι) : inner ℂ (b i) ((S * B * S) (b i)) =
      inner ℂ (S (b i)) (B (S (b i))) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← S.adjoint_inner_left, hS.adjoint_eq]
  rw [positiveTrace_eq_tsum_diagonal b (conjugate_nonneg_of_nonneg hB (CFC.sqrt_nonneg A))]
  change (∑' i, ENNReal.ofReal (inner ℂ (b i) ((S * B * S) (b i))).re) = _
  simp_rw [hdiag]
  have hn (i : ι) : 0 ≤ (inner ℂ (S (b i)) (B (S (b i)))).re :=
    (nonneg_iff_isPositive.mp hB).re_inner_nonneg_right _
  have hs := Complex.hasSum_re
    (summable_familyExpectation_terms (fun i => S (b i))
      (summable_sqrt_basis_norm_sq b hA) B).hasSum
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq]
  rfl

theorem density_sandwich_isPositiveTraceClass (b : HilbertBasis ι ℂ E)
    {A : E →L[ℂ] E} (hA : IsPositiveTraceClass A) {B : E →L[ℂ] E} (hB : 0 ≤ B) :
    IsPositiveTraceClass (CFC.sqrt A * B * CFC.sqrt A) := by
  refine ⟨conjugate_nonneg_of_nonneg hB (CFC.sqrt_nonneg A), ?_⟩
  rw [positiveTrace_density_sandwich b hA hB]
  exact ENNReal.ofReal_lt_top

/-- The state whose expectation is given by the trace pairing with a positive trace-one density. -/
def positiveDensityState (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) (htrace : positiveTrace A = 1) : State E :=
  familyState (fun i => CFC.sqrt A (b i))
    (summable_sqrt_basis_norm_sq b ⟨hA, by rw [htrace]; exact ENNReal.one_lt_top⟩)
    (by rw [tsum_sqrt_basis_norm_sq b ⟨hA, by rw [htrace]; exact ENNReal.one_lt_top⟩,
      htrace, ENNReal.toReal_one])

@[simp] theorem positiveDensityState_apply (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E}
    (hA : 0 ≤ A) (htrace : positiveTrace A = 1) (B : E →L[ℂ] E) :
    positiveDensityState b hA htrace B = densityExpectation b A B := rfl

end VacuumBellSeparation.Gaussian
