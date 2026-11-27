/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HermitianTraceRemainder

/-!
# A quadratic norm remainder for an actual Hermitian spectral trace

The overlap-weighted squared eigenvalue differences equal the actual
trace of (B-A)². Spectral calculus bounds that trace by dimension times
the squared operator norm. A scalar Taylor remainder therefore gives a
genuine quadratic remainder for Tr f(B), including repeated eigenvalues.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_trace_sq_sub_eq_overlap {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((B - A) ^ 2).trace.re =
      ∑ i, ∑ j, unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (hB.eigenvalues j - hA.eigenvalues i) ^ 2 := by
  have h := real_trace_cfc_remainder hA hB (fun x => x ^ 2) (fun x => 2 * x)
  rw [cfc_pow_id B 2 hB.isSelfAdjoint, cfc_pow_id A 2 hA.isSelfAdjoint,
    cfc_const_mul_id (2 : ℝ) A hA.isSelfAdjoint] at h
  have ht : (B ^ 2 - A ^ 2 - (2 : ℝ) • A * (B - A)).trace =
      ((B - A) ^ 2).trace := by
    simp only [two_smul, pow_two, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.trace_sub, Matrix.trace_add]
    rw [Matrix.trace_mul_comm B A]
    abel
  rw [ht] at h
  calc
    _ = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem real_trace_sq_le_card_norm_sq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace.re ≤ (Fintype.card ι : ℝ) * ‖A‖ ^ 2 := by
  have h := real_matrix_trace_cfc hA (fun x => x ^ 2)
  rw [cfc_pow_id A 2 hA.isSelfAdjoint] at h
  rw [h]
  calc
    ∑ i, hA.eigenvalues i ^ 2 ≤ ∑ _i : ι, ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hb : |hA.eigenvalues i| ≤ ‖A‖ := by
        simpa only [Real.norm_eq_abs] using
          IsometricContinuousFunctionalCalculus.norm_spectrum_le A
            (hA.eigenvalues_mem_spectrum_real i) hA.isSelfAdjoint
      nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i), norm_nonneg A]
    _ = _ := by simp

theorem abs_real_trace_cfc_remainder_le_trace_sq {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f d : ℝ → ℝ) (C : ℝ)
    (hrem : ∀ i j, |f (hB.eigenvalues j) - f (hA.eigenvalues i) -
      d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)| ≤
        C * (hB.eigenvalues j - hA.eigenvalues i) ^ 2) :
    |(cfc f B - cfc f A - cfc d A * (B - A)).trace.re| ≤
      C * ((B - A) ^ 2).trace.re := by
  rw [real_trace_sq_sub_eq_overlap hA hB]
  exact abs_real_trace_cfc_remainder_le hA hB f d C hrem

/-- A scalar second-order bound controls the actual matrix trace in the
operator norm; no differentiable eigenvalue enumeration is required. -/
theorem abs_real_trace_cfc_remainder_le_norm_sq {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f d : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ i j, |f (hB.eigenvalues j) - f (hA.eigenvalues i) -
      d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)| ≤
        C * (hB.eigenvalues j - hA.eigenvalues i) ^ 2) :
    |(cfc f B - cfc f A - cfc d A * (B - A)).trace.re| ≤
      (C * Fintype.card ι) * ‖B - A‖ ^ 2 := by
  calc
    _ ≤ C * ((B - A) ^ 2).trace.re :=
      abs_real_trace_cfc_remainder_le_trace_sq hA hB f d C hrem
    _ ≤ C * ((Fintype.card ι : ℝ) * ‖B - A‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (real_trace_sq_le_card_norm_sq (hB.sub hA)) hC
    _ = _ := by ring

end VacuumBellSeparation.Gaussian
