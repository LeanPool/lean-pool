/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IndexedDiagonalDensity
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalState

/-!
# Probability-weighted diagonal states on arbitrary Hilbert bases

This extends the actual number-basis series construction to arbitrary
Hilbert-basis indices. Absolute convergence defines the complex state;
positive inputs agree with the positive trace of the actual square-root
sandwich. The existing natural-index proof is reused with index generality,
without treating the positive trace as a complex trace on arbitrary inputs.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder ENNReal

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Indexed diagonal expectation given by `∑' k, (w k : ℂ) * inner ℂ (b k) (A (b k))`. -/
noncomputable def indexedDiagonalExpectation (b : HilbertBasis ι ℂ E) (w : ι → ℝ)
    (A : E →L[ℂ] E) : ℂ := ∑' k, (w k : ℂ) * inner ℂ (b k) (A (b k))

omit [CompleteSpace E] in
theorem norm_indexedDiagonalExpectation_term_le (b : HilbertBasis ι ℂ E)
    (w : ι → ℝ) (A : E →L[ℂ] E) (k : ι) :
    ‖(w k : ℂ) * inner ℂ (b k) (A (b k))‖ ≤ |w k| * ‖A‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖inner ℂ (b k) (A (b k))‖ ≤ ‖b k‖ * ‖A (b k)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b k‖ * (‖A‖ * ‖b k‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = ‖A‖ := by rw [b.orthonormal.norm_eq_one]; ring

omit [CompleteSpace E] in
theorem summable_indexedDiagonalExpectation_terms (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    Summable fun k => (w k : ℂ) * inner ℂ (b k) (A (b k)) := by
  have hwabs : Summable fun k => |w k| := by
    simpa only [Real.norm_eq_abs] using hw.norm
  apply (hwabs.mul_right ‖A‖).of_norm_bounded
  exact norm_indexedDiagonalExpectation_term_le b w A

omit [CompleteSpace E] in
theorem norm_indexedDiagonalExpectation_le (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    ‖indexedDiagonalExpectation b w A‖ ≤ (∑' k, |w k|) * ‖A‖ := by
  have hwabs : Summable fun k => |w k| := by
    simpa only [Real.norm_eq_abs] using hw.norm
  exact tsum_of_norm_bounded (hwabs.hasSum.mul_right ‖A‖)
    (norm_indexedDiagonalExpectation_term_le b w A)

/-- Continuous linear map for the indexed diagonal expectation linear, of type `(E →L[ℂ] E) →ₗ[ℂ] ℂ
where toFun`. -/
noncomputable def indexedDiagonalExpectationLinear (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) : (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := indexedDiagonalExpectation b w
  map_add' A B := by
    simp only [indexedDiagonalExpectation, add_apply, inner_add_right, mul_add]
    exact Summable.tsum_add (summable_indexedDiagonalExpectation_terms b hw A)
      (summable_indexedDiagonalExpectation_terms b hw B)
  map_smul' c A := by
    simp only [indexedDiagonalExpectation, smul_apply, inner_smul_right, RingHom.id_apply,
      smul_eq_mul]
    simp_rw [mul_left_comm (w _ : ℂ) c]
    exact tsum_mul_left

/-- Indexed diagonal expectation continuous linear map of type `(E →L[ℂ] E) →L[ℂ] ℂ`. -/
noncomputable def indexedDiagonalExpectationCLM (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  (indexedDiagonalExpectationLinear b hw).mkContinuous (∑' k, |w k|)
    (norm_indexedDiagonalExpectation_le b hw)

omit [CompleteSpace E] in
@[simp] theorem indexedDiagonalExpectationCLM_apply (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    indexedDiagonalExpectationCLM b hw A = indexedDiagonalExpectation b w A := rfl

omit [CompleteSpace E] in
theorem indexedDiagonalExpectation_one (b : HilbertBasis ι ℂ E) (w : ι → ℝ) :
    indexedDiagonalExpectation b w 1 = (∑' k, w k : ℝ) := by
  simp only [indexedDiagonalExpectation, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one, RCLike.ofReal_one, one_pow, mul_one]
  exact (Complex.ofReal_tsum w).symm

omit [CompleteSpace E] in
theorem indexedDiagonalExpectation_nonneg (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    0 ≤ indexedDiagonalExpectation b w A := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (Complex.zero_le_real.mpr (hw k))
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_nonneg_right (b k))

/-- A probability-weighted diagonal series is a state on the actual bounded
operator algebra. Normality is not being asserted by this bundled type. -/
noncomputable def indexedDiagonalState (b : HilbertBasis ι ℂ E) {w : ι → ℝ}
    (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : ∑' k, w k = 1) : State E where
  toLinearMap := indexedDiagonalExpectationLinear b hw
  map_one' := by
    change indexedDiagonalExpectation b w 1 = 1
    simpa only [hw₁, Complex.ofReal_one] using indexedDiagonalExpectation_one b w
  map_nonneg' A hA := by
    have h := Complex.nonneg_iff.mp (indexedDiagonalExpectation_nonneg b hw₀
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA))
    exact ⟨h.2.symm, h.1⟩

theorem sqrt_indexedDiagonalOperator_apply_basis (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (k : ι) :
    CFC.sqrt (indexedDiagonalOperator b w) (b k) = Real.sqrt (w k) • b k := by
  have hk : b k ≠ 0 := by
    intro hz
    have hn := b.orthonormal.norm_eq_one k
    rw [hz, norm_zero] at hn
    norm_num at hn
  have heig := indexedDiagonalOperator_apply_basis b hw k
  rw [CFC.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact rpow_apply_eigenvector (indexedDiagonalOperator_nonneg b hw₀)
    (eigenvalue_mem_real_spectrum hk heig) heig (by norm_num)

theorem positiveTrace_indexedDiagonal_sandwich (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (indexedDiagonalOperator b w) * A * CFC.sqrt
      (indexedDiagonalOperator b w)) =
      ENNReal.ofReal (indexedDiagonalExpectation b w A).re := by
  let S := CFC.sqrt (indexedDiagonalOperator b w)
  have hs : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hdiag (k : ι) : inner ℂ (b k) ((S * A * S) (b k)) =
      (w k : ℂ) * inner ℂ (b k) (A (b k)) := by
    calc
      inner ℂ (b k) ((S * A * S) (b k)) =
          inner ℂ (S (b k)) (A (S (b k))) := by
        rw [mul_apply_eq_comp, mul_apply_eq_comp,
          ← S.adjoint_inner_left, hs.adjoint_eq]
      _ = _ := by
        change inner ℂ (CFC.sqrt (indexedDiagonalOperator b w) (b k))
          (A (CFC.sqrt (indexedDiagonalOperator b w) (b k))) = _
        rw [sqrt_indexedDiagonalOperator_apply_basis b hw hw₀,
          map_smul_of_tower, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
        simp only [Algebra.smul_def, Complex.coe_algebraMap]
        rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw₀ k)]
  rw [positiveTrace_eq_tsum_diagonal b
    (conjugate_nonneg_of_nonneg hA (CFC.sqrt_nonneg _))]
  change (∑' k, ENNReal.ofReal (inner ℂ (b k) ((S * A * S) (b k))).re) = _
  simp_rw [hdiag]
  have hnonneg (k : ι) : 0 ≤ ((w k : ℂ) * inner ℂ (b k) (A (b k))).re :=
    (Complex.nonneg_iff.mp (mul_nonneg (Complex.zero_le_real.mpr (hw₀ k))
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_nonneg_right _))).1
  have hsum := Complex.hasSum_re (summable_indexedDiagonalExpectation_terms b hw A).hasSum
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable, hsum.tsum_eq]
  rfl

end VacuumBellSeparation.Gaussian
