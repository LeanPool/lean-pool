/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order

/-!
# Actual unitary overlaps between finite eigenbases

The squared absolute entries of an actual unitary matrix have unit row
and column sums. They give the exact real diagonal and mixed trace under
unitary conjugation. These finite identities are the ingredients for a
spectral trace Taylor estimate that does not differentiate eigenbranches.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary overlap weight given by `‖(U : Matrix ι ι ℂ) i j‖ ^ 2`. -/
def unitaryOverlapWeight (U : unitary (Matrix ι ι ℂ)) (i j : ι) : ℝ :=
  ‖(U : Matrix ι ι ℂ) i j‖ ^ 2

theorem unitaryOverlapWeight_nonneg (U : unitary (Matrix ι ι ℂ)) (i j : ι) :
    0 ≤ unitaryOverlapWeight U i j := sq_nonneg _

theorem sum_unitaryOverlapWeight_row (U : unitary (Matrix ι ι ℂ)) (i : ι) :
    ∑ j, unitaryOverlapWeight U i j = 1 := by
  have he : ((U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ) i i =
      ((∑ j, unitaryOverlapWeight U i j : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply,
      RCLike.mul_conj, unitaryOverlapWeight]
    norm_cast
  have hU : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  rw [hU, Matrix.one_apply_eq] at he
  exact_mod_cast he.symm

theorem sum_unitaryOverlapWeight_col (U : unitary (Matrix ι ι ℂ)) (j : ι) :
    ∑ i, unitaryOverlapWeight U i j = 1 := by
  have he : ((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) j j =
      ((∑ i, unitaryOverlapWeight U i j : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply,
      RCLike.conj_mul, unitaryOverlapWeight]
    norm_cast
  have hU : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hU, Matrix.one_apply_eq] at he
  exact_mod_cast he.symm

theorem diagonal_unitary_real_conjugate (U : unitary (Matrix ι ι ℂ))
    (d : ι → ℝ) (i : ι) :
    ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (d j : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ) i i =
        ((∑ j, d j * unitaryOverlapWeight U i j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [← starRingEnd_apply]
  change (U : Matrix ι ι ℂ) i j * (d j : ℂ) * conj ((U : Matrix ι ι ℂ) i j) = _
  calc
    _ = (d j : ℂ) * ((U : Matrix ι ι ℂ) i j * conj ((U : Matrix ι ι ℂ) i j)) := by ring
    _ = _ := by
      rw [Complex.mul_conj']
      simp only [unitaryOverlapWeight, Complex.ofReal_pow]

theorem real_diagonal_unitary_real_conjugate (U : unitary (Matrix ι ι ℂ))
    (d : ι → ℝ) (i : ι) :
    (((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (d j : ℂ)) *
      (U : Matrix ι ι ℂ)ᴴ) i i).re =
        ∑ j, d j * unitaryOverlapWeight U i j := by
  rw [diagonal_unitary_real_conjugate, Complex.ofReal_re]

theorem real_trace_mixed_unitary_diagonals (U : unitary (Matrix ι ι ℂ))
    (a b : ι → ℝ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
        (U : Matrix ι ι ℂ)ᴴ)).trace.re =
      ∑ i, ∑ j, a i * b j * unitaryOverlapWeight U i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Matrix.diagonal_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_diagonal_unitary_real_conjugate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unitaryOverlapWeight_sum_left (U : unitary (Matrix ι ι ℂ)) (f : ι → ℝ) :
    ∑ i, ∑ j, unitaryOverlapWeight U i j * f i = ∑ i, f i := by
  simp only [← Finset.sum_mul, sum_unitaryOverlapWeight_row, one_mul]

theorem unitaryOverlapWeight_sum_right (U : unitary (Matrix ι ι ℂ)) (f : ι → ℝ) :
    ∑ i, ∑ j, unitaryOverlapWeight U i j * f j = ∑ j, f j := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_unitaryOverlapWeight_col, one_mul]

end VacuumBellSeparation.Gaussian
