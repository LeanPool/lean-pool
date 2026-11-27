/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers

/-!
# Summable diagonal densities indexed by an arbitrary Hilbert basis

This generalizes the number-sequence rank-one construction to arbitrary
basis indices, including the multi-indices of a finite-mode oscillator.
All evaluation and trace statements require actual summability. The
sequence construction agrees definitionally at index ℕ.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap InnerProductSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

/-- A diagonal operator specified by an absolutely summable real family.
The convergence hypothesis is required in the evaluation theorems. -/
noncomputable def indexedDiagonalOperator (b : HilbertBasis ι ℂ E) (w : ι → ℝ) :
    E →L[ℂ] E := ∑' k, w k • rankOne ℂ (b k) (b k)

theorem summable_indexedDiagonalOperator_terms (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) :
    Summable fun k => w k • rankOne ℂ (b k) (b k) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one, mul_one] using hw.norm

theorem indexedDiagonalOperator_nonneg (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) : 0 ≤ indexedDiagonalOperator b w := by
  apply tsum_nonneg
  intro k
  exact smul_nonneg (hw k)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self (b k)))

theorem indexedDiagonalOperator_apply_basis (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (k : ι) :
    indexedDiagonalOperator b w (b k) = w k • b k := by
  classical
  rw [indexedDiagonalOperator, tsum_apply (summable_indexedDiagonalOperator_terms b hw)]
  rw [tsum_eq_single k]
  · simp [rankOne_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  · intro j hj
    simp [rankOne_apply, b.orthonormal.inner_eq_zero hj]

theorem indexedDiagonalOperator_inner (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (x : E) (k : ι) :
    inner ℂ (b k) (indexedDiagonalOperator b w x) =
      (w k : ℂ) * inner ℂ (b k) x := by
  have hA := (indexedDiagonalOperator_nonneg b hw₀).isSelfAdjoint
  simpa only [hA.adjoint_eq, indexedDiagonalOperator_apply_basis b hw,
    inner_smul_left_eq_smul, Algebra.smul_def, Complex.coe_algebraMap] using
    ((indexedDiagonalOperator b w).adjoint_inner_left x (b k)).symm

theorem indexedDiagonalOperator_injective (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hwpos : ∀ k, 0 < w k) :
    Function.Injective (indexedDiagonalOperator b w) := by
  intro x y hxy
  apply b.repr.injective
  ext k
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have h := congrArg (fun z => inner ℂ (b k) z) hxy
  rw [indexedDiagonalOperator_inner b hw (fun k => (hwpos k).le),
    indexedDiagonalOperator_inner b hw (fun k => (hwpos k).le)] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hwpos k))) h

theorem positiveTrace_indexedDiagonalOperator (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) :
    positiveTrace (indexedDiagonalOperator b w) = ENNReal.ofReal (∑' k, w k) := by
  rw [positiveTrace_eq_tsum_diagonal b (indexedDiagonalOperator_nonneg b hw₀),
    ENNReal.ofReal_tsum_of_nonneg hw₀ hw]
  apply tsum_congr
  intro k
  rw [indexedDiagonalOperator_apply_basis b hw, inner_smul_right_eq_smul,
    inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Algebra.smul_def]

omit [CompleteSpace E] in
theorem indexedDiagonalOperator_nat_eq (b : HilbertBasis ℕ ℂ E) (w : ℕ → ℝ) :
    indexedDiagonalOperator b w = diagonalOperator b w := rfl

theorem indexedDiagonalOperator_rpow_apply_basis (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    {τ : ℝ} (hτ : 0 < τ) (i : ι) :
    (indexedDiagonalOperator b w ^ τ) (b i) = w i ^ τ • b i := by
  have hi : b i ≠ 0 := by
    intro hz
    have hn := b.orthonormal.norm_eq_one i
    rw [hz, norm_zero] at hn
    norm_num at hn
  have heig := indexedDiagonalOperator_apply_basis b hw i
  exact rpow_apply_eigenvector (indexedDiagonalOperator_nonneg b hw₀)
    (eigenvalue_mem_real_spectrum hi heig) heig hτ

theorem positiveTrace_indexedDiagonalOperator_rpow (b : HilbertBasis ι ℂ E)
    {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    {τ : ℝ} (hτ : 0 < τ) (hs : Summable fun i => w i ^ τ) :
    positiveTrace (indexedDiagonalOperator b w ^ τ) = ENNReal.ofReal (∑' i, w i ^ τ) := by
  rw [positiveTrace_eq_tsum_diagonal b CFC.rpow_nonneg,
    ENNReal.ofReal_tsum_of_nonneg (fun i => Real.rpow_nonneg (hw₀ i) τ) hs]
  apply tsum_congr
  intro i
  rw [indexedDiagonalOperator_rpow_apply_basis b hw hw₀ hτ,
    inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Algebra.smul_def]

end VacuumBellSeparation.Gaussian
