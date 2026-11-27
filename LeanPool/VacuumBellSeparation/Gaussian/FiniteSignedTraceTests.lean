/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityTraceNormDual
public import LeanPool.VacuumBellSeparation.Gaussian.DensityOffDiagonalInversion

/-!
# Actual finite signed trace tests on a Hilbert space

A finite weighted orthonormal projection is a contraction when its scalar
weights have modulus at most one. Its pairing against a two-sided product
is identified with the actual Jordan density expectation. This gives the
nuclear dual upper bound without assuming a complex trace or cyclicity.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap InnerProductSpace
open scoped ComplexConjugate ENNReal

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Finite trace test operator given by `∑ i ∈ s, w i • rankOne ℂ (u i) (u i)`. -/
def finiteTraceTestOperator (u : ι → E) (s : Finset ι) (w : ι → ℂ) : E →L[ℂ] E :=
  ∑ i ∈ s, w i • rankOne ℂ (u i) (u i)

/-- Finite trace test given by `∑ i ∈ s, w i • ((innerSL ℂ (u i)).comp (ContinuousLinearMap.apply ℂ
E (u i)))`. -/
def finiteTraceTest (u : ι → E) (s : Finset ι) (w : ι → ℂ) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  ∑ i ∈ s, w i • ((innerSL ℂ (u i)).comp (ContinuousLinearMap.apply ℂ E (u i)))

omit [CompleteSpace E] in
@[simp] theorem finiteTraceTest_apply (u : ι → E) (s : Finset ι) (w : ι → ℂ)
    (A : E →L[ℂ] E) : finiteTraceTest u s w A = ∑ i ∈ s, w i * inner ℂ (u i) (A (u i)) := by
  simp only [finiteTraceTest, sum_apply, smul_apply, comp_apply, innerSL_apply_apply,
    apply_apply, smul_eq_mul]

omit [CompleteSpace E] in
@[simp] theorem finiteTraceTestOperator_apply (u : ι → E) (s : Finset ι) (w : ι → ℂ)
    (x : E) : finiteTraceTestOperator u s w x =
      ∑ i ∈ s, (w i * inner ℂ (u i) x) • u i := by
  simp only [finiteTraceTestOperator, sum_apply, smul_apply, rankOne_apply, smul_smul]

omit [CompleteSpace E] in
theorem norm_finiteTraceTestOperator_le_one {u : ι → E} (hu : Orthonormal ℂ u)
    (s : Finset ι) (w : ι → ℂ) (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) :
    ‖finiteTraceTestOperator u s w‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have he : ‖finiteTraceTestOperator u s w x‖ ^ 2 =
      ∑ i ∈ s, ‖w i * inner ℂ (u i) x‖ ^ 2 := by
    rw [finiteTraceTestOperator_apply, norm_sq_eq_re_inner (𝕜 := ℂ), hu.inner_sum]
    simp only [map_sum, Complex.conj_mul', ← Complex.ofReal_pow,
      RCLike.re_eq_complex_re, Complex.ofReal_re]
  have hs : ‖finiteTraceTestOperator u s w x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [he]
    apply (Finset.sum_le_sum fun i hi => ?_).trans (hu.sum_inner_products_le x)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i hi) (norm_nonneg _)
  rw [one_mul]
  nlinarith [norm_nonneg (finiteTraceTestOperator u s w x), norm_nonneg x]

theorem selfAdjoint_parts_traceClass {B : E →L[ℂ] E} (hB : IsSelfAdjoint B)
    (ht : operatorTraceNorm B < ∞) :
    IsPositiveTraceClass B⁺ ∧ IsPositiveTraceClass B⁻ := by
  have ha : IsPositiveTraceClass (CFC.abs B) := ⟨CFC.abs_nonneg B, ht⟩
  constructor
  · apply ha.of_le (CFC.posPart_nonneg B)
    rw [← CFC.posPart_add_negPart B hB]
    exact le_add_of_nonneg_right (CFC.negPart_nonneg B)
  · apply ha.of_le (CFC.negPart_nonneg B)
    rw [← CFC.posPart_add_negPart B hB]
    exact le_add_of_nonneg_left (CFC.posPart_nonneg B)

/-- Jordan expectation given by `densityExpectation b B⁺ A - densityExpectation b B⁻ A`. -/
def jordanExpectation (b : HilbertBasis κ ℂ E) (B A : E →L[ℂ] E) : ℂ :=
  densityExpectation b B⁺ A - densityExpectation b B⁻ A

/-- Jordan expectation continuous linear map of type `(E →L[ℂ] E) →L[ℂ] ℂ`. -/
def jordanExpectationCLM (b : HilbertBasis κ ℂ E) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  densityExpectationCLM b (selfAdjoint_parts_traceClass hB ht).1 -
    densityExpectationCLM b (selfAdjoint_parts_traceClass hB ht).2

@[simp] theorem jordanExpectationCLM_apply (b : HilbertBasis κ ℂ E) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞) (A : E →L[ℂ] E) :
    jordanExpectationCLM b hB ht A = jordanExpectation b B A := rfl

theorem norm_jordanExpectation_le (b : HilbertBasis κ ℂ E) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞) (A : E →L[ℂ] E) :
    ‖jordanExpectation b B A‖ ≤ (operatorTraceNorm B).toReal * ‖A‖ := by
  obtain ⟨hp, hn⟩ := selfAdjoint_parts_traceClass hB ht
  simpa only [jordanExpectation, CFC.posPart_sub_negPart B hB] using
    norm_densityExpectation_sub_le_traceNorm b hp hn A

theorem jordanExpectation_rankOne (b : HilbertBasis κ ℂ E) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (x y : E) :
    jordanExpectation b B (rankOne ℂ x y) = inner ℂ y (B x) := by
  rw [jordanExpectation, densityExpectation_rankOne_mixed b (CFC.posPart_nonneg B),
    densityExpectation_rankOne_mixed b (CFC.negPart_nonneg B), ← inner_sub_right,
    ← sub_apply, CFC.posPart_sub_negPart B hB]

theorem finiteTraceTestOperator_two_sided (u : ι → E) (s : Finset ι) (w : ι → ℂ)
    (L R : E →L[ℂ] E) : R * finiteTraceTestOperator u s w * L =
      ∑ i ∈ s, w i • rankOne ℂ (R (u i)) (L.adjoint (u i)) := by
  ext x
  simp only [mul_apply_eq_comp, finiteTraceTestOperator_apply, map_sum, map_smul,
    sum_apply, smul_apply, rankOne_apply, smul_smul, adjoint_inner_left]

theorem finiteTraceTest_two_sided (b : HilbertBasis κ ℂ E) (u : ι → E)
    (s : Finset ι) (w : ι → ℂ) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞) (L R : E →L[ℂ] E) :
    finiteTraceTest u s w (L * B * R) =
      jordanExpectation b B (R * finiteTraceTestOperator u s w * L) := by
  rw [← jordanExpectationCLM_apply b hB ht,
    finiteTraceTestOperator_two_sided, map_sum]
  simp only [map_smul, jordanExpectationCLM_apply, jordanExpectation_rankOne b hB,
    finiteTraceTest_apply, mul_apply_eq_comp, adjoint_inner_left, smul_eq_mul]

theorem norm_finiteTraceTest_two_sided_le (b : HilbertBasis κ ℂ E) {u : ι → E}
    (hu : Orthonormal ℂ u) (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) {B : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (ht : operatorTraceNorm B < ∞) (L R : E →L[ℂ] E) :
    ‖finiteTraceTest u s w (L * B * R)‖ ≤
      (operatorTraceNorm B).toReal * (‖R‖ * ‖L‖) := by
  rw [finiteTraceTest_two_sided b u s w hB ht]
  apply (norm_jordanExpectation_le b hB ht _).trans
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc
    ‖R * finiteTraceTestOperator u s w * L‖ ≤
        ‖R‖ * ‖finiteTraceTestOperator u s w‖ * ‖L‖ := norm_mul₃_le
    _ ≤ ‖R‖ * 1 * ‖L‖ := by
      gcongr
      exact norm_finiteTraceTestOperator_le_one hu s w hw
    _ = ‖R‖ * ‖L‖ := by rw [mul_one]

end VacuumBellSeparation.Gaussian
