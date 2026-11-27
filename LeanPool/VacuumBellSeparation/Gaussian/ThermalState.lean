/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers
public import LeanPool.VacuumBellSeparation.Gaussian.HilbertSchmidtTrace
public import LeanPool.VacuumBellSeparation.Bell.Defs

/-!
# Thermal expectations as actual bounded states

A summable diagonal density defines a complex-linear functional by its
absolutely convergent number-basis series. Positive inputs agree with the
positive trace of the square-root sandwich. No value of the positive trace
on a nonpositive operator is used to define a complex trace.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexOrder ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Diagonal expectation given by `∑' k, (w k : ℂ) * inner ℂ (b k) (A (b k))`. -/
noncomputable def diagonalExpectation (b : HilbertBasis ℕ ℂ E) (w : ℕ → ℝ)
    (A : E →L[ℂ] E) : ℂ := ∑' k, (w k : ℂ) * inner ℂ (b k) (A (b k))

omit [CompleteSpace E] in
theorem norm_diagonalExpectation_term_le (b : HilbertBasis ℕ ℂ E)
    (w : ℕ → ℝ) (A : E →L[ℂ] E) (k : ℕ) :
    ‖(w k : ℂ) * inner ℂ (b k) (A (b k))‖ ≤ |w k| * ‖A‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖inner ℂ (b k) (A (b k))‖ ≤ ‖b k‖ * ‖A (b k)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b k‖ * (‖A‖ * ‖b k‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = ‖A‖ := by rw [b.orthonormal.norm_eq_one]; ring

omit [CompleteSpace E] in
theorem summable_diagonalExpectation_terms (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    Summable fun k => (w k : ℂ) * inner ℂ (b k) (A (b k)) := by
  have hwabs : Summable fun k => |w k| := by
    simpa only [Real.norm_eq_abs] using hw.norm
  apply (hwabs.mul_right ‖A‖).of_norm_bounded
  exact norm_diagonalExpectation_term_le b w A

omit [CompleteSpace E] in
theorem norm_diagonalExpectation_le (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    ‖diagonalExpectation b w A‖ ≤ (∑' k, |w k|) * ‖A‖ := by
  have hwabs : Summable fun k => |w k| := by
    simpa only [Real.norm_eq_abs] using hw.norm
  exact tsum_of_norm_bounded (hwabs.hasSum.mul_right ‖A‖)
    (norm_diagonalExpectation_term_le b w A)

/-- Continuous linear map for the diagonal expectation linear, of type `(E →L[ℂ] E) →ₗ[ℂ] ℂ where
toFun`. -/
noncomputable def diagonalExpectationLinear (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) : (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := diagonalExpectation b w
  map_add' A B := by
    simp only [diagonalExpectation, add_apply, inner_add_right, mul_add]
    exact (summable_diagonalExpectation_terms b hw A).tsum_add
      (summable_diagonalExpectation_terms b hw B)
  map_smul' c A := by
    simp only [diagonalExpectation, smul_apply, inner_smul_right, RingHom.id_apply,
      smul_eq_mul]
    simp_rw [mul_left_comm (w _ : ℂ) c]
    exact tsum_mul_left

/-- Diagonal expectation continuous linear map of type `(E →L[ℂ] E) →L[ℂ] ℂ`. -/
noncomputable def diagonalExpectationCLM (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  (diagonalExpectationLinear b hw).mkContinuous (∑' k, |w k|)
    (norm_diagonalExpectation_le b hw)

omit [CompleteSpace E] in
@[simp] theorem diagonalExpectationCLM_apply (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (A : E →L[ℂ] E) :
    diagonalExpectationCLM b hw A = diagonalExpectation b w A := rfl

omit [CompleteSpace E] in
theorem diagonalExpectation_one (b : HilbertBasis ℕ ℂ E) (w : ℕ → ℝ) :
    diagonalExpectation b w 1 = (∑' k, w k : ℝ) := by
  simp only [diagonalExpectation, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one, RCLike.ofReal_one, one_pow, mul_one]
  exact (Complex.ofReal_tsum w).symm

omit [CompleteSpace E] in
theorem diagonalExpectation_nonneg (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    0 ≤ diagonalExpectation b w A := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (Complex.zero_le_real.mpr (hw k))
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_nonneg_right (b k))

/-- A probability-weighted diagonal series is a state on the actual bounded
operator algebra. Normality is not being asserted by this bundled type. -/
noncomputable def diagonalState (b : HilbertBasis ℕ ℂ E) {w : ℕ → ℝ}
    (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : ∑' k, w k = 1) : State E where
  toLinearMap := diagonalExpectationLinear b hw
  map_one' := by simpa [diagonalExpectationLinear, hw₁] using diagonalExpectation_one b w
  map_nonneg' A hA := by
    have h := Complex.nonneg_iff.mp (diagonalExpectation_nonneg b hw₀
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA))
    exact ⟨h.2.symm, h.1⟩

theorem sqrt_diagonalOperator_apply_basis (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (k : ℕ) :
    CFC.sqrt (diagonalOperator b w) (b k) = Real.sqrt (w k) • b k := by
  have hk : b k ≠ 0 := by
    intro hz
    have hn := b.orthonormal.norm_eq_one k
    rw [hz, norm_zero] at hn
    norm_num at hn
  have heig := diagonalOperator_apply_basis b hw k
  rw [CFC.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact rpow_apply_eigenvector (diagonalOperator_nonneg b hw₀)
    (eigenvalue_mem_real_spectrum hk heig) heig (by norm_num)

theorem positiveTrace_diagonal_sandwich (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k)
    {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (diagonalOperator b w) * A * CFC.sqrt (diagonalOperator b w)) =
      ENNReal.ofReal (diagonalExpectation b w A).re := by
  let S := CFC.sqrt (diagonalOperator b w)
  have hs : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hdiag (k : ℕ) : inner ℂ (b k) ((S * A * S) (b k)) =
      (w k : ℂ) * inner ℂ (b k) (A (b k)) := by
    calc
      inner ℂ (b k) ((S * A * S) (b k)) =
          inner ℂ (S (b k)) (A (S (b k))) := by
        rw [mul_apply_eq_comp, mul_apply_eq_comp,
          ← S.adjoint_inner_left, hs.adjoint_eq]
      _ = _ := by
        change inner ℂ (CFC.sqrt (diagonalOperator b w) (b k))
          (A (CFC.sqrt (diagonalOperator b w) (b k))) = _
        rw [sqrt_diagonalOperator_apply_basis b hw hw₀,
          map_smul_of_tower, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
        simp only [Algebra.smul_def, Complex.coe_algebraMap]
        rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw₀ k)]
  rw [positiveTrace_eq_tsum_diagonal b
    (conjugate_nonneg_of_nonneg hA (CFC.sqrt_nonneg _))]
  change (∑' k, ENNReal.ofReal (inner ℂ (b k) ((S * A * S) (b k))).re) = _
  simp_rw [hdiag]
  have hnonneg (k : ℕ) : 0 ≤ ((w k : ℂ) * inner ℂ (b k) (A (b k))).re :=
    (Complex.nonneg_iff.mp (mul_nonneg (Complex.zero_le_real.mpr (hw₀ k))
      ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).inner_nonneg_right _))).1
  have hsum := Complex.hasSum_re (summable_diagonalExpectation_terms b hw A).hasSum
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable, hsum.tsum_eq]
  rfl

/-- Thermal state. -/
noncomputable def thermalState {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    State OscillatorSpace :=
  diagonalState numberBasis (hasSum_thermalWeight hq₀ hq₁).summable
    (fun k => mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k))
    (hasSum_thermalWeight hq₀ hq₁).tsum_eq

theorem thermalState_apply {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (A : OscillatorSpace →L[ℂ] OscillatorSpace) :
    thermalState hq₀ hq₁ A = ∑' k, (thermalWeight q k : ℂ) *
      inner ℂ (numberBasis k) (A (numberBasis k)) := rfl

theorem norm_thermalState_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (A : OscillatorSpace →L[ℂ] OscillatorSpace) : ‖thermalState hq₀ hq₁ A‖ ≤ ‖A‖ := by
  have hw₀ (k : ℕ) : 0 ≤ thermalWeight q k :=
    mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)
  change ‖diagonalExpectation numberBasis (thermalWeight q) A‖ ≤ ‖A‖
  have h := norm_diagonalExpectation_le numberBasis
    (hasSum_thermalWeight hq₀ hq₁).summable A
  simpa only [abs_of_nonneg (hw₀ _), (hasSum_thermalWeight hq₀ hq₁).tsum_eq,
    one_mul] using h

theorem positiveTrace_thermal_sandwich {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    {A : OscillatorSpace →L[ℂ] OscillatorSpace} (hA : 0 ≤ A) :
    positiveTrace (CFC.sqrt (thermalDensity q) * A * CFC.sqrt (thermalDensity q)) =
      ENNReal.ofReal (thermalState hq₀ hq₁ A).re :=
  positiveTrace_diagonal_sandwich numberBasis (hasSum_thermalWeight hq₀ hq₁).summable
    (fun k => mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)) hA

end VacuumBellSeparation.Gaussian
