/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixResolventBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The genuine matrix logarithm and determinant perturbation bound

Finite spectral calculus identifies Tr log A with log det A on the
strict positive cone. The scalar logarithm estimate then proves the
source bound for I-Z using the actual nuclear norm of the symmetric Z.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_trace_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]

theorem matrix_det_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).det = ∏ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq]
  simp [Matrix.IsHermitian.cfc, -Unitary.conjStarAlgAut_apply]

theorem matrix_trace_log_eq_log_det {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (cfc Real.log A).trace = Real.log A.det := by
  rw [matrix_trace_cfc hA.isHermitian, hA.isHermitian.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]

theorem real_log_one_sub_bound {x δ : ℝ} (hδ : δ < 1) (hx : |x| ≤ δ) :
    |Real.log (1 - x)| ≤ |x| / (1 - δ) := by
  have h := Real.abs_log_sub_add_sum_range_le (hx.trans_lt hδ) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, zero_add, pow_one] at h
  exact h.trans (div_le_div_of_nonneg_left (abs_nonneg x) (sub_pos.mpr hδ)
    (by linarith))

theorem abs_log_det_one_sub_le {Z : Matrix ι ι ℝ}
    (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) :
    |Real.log (1 - Z).det| ≤ matrixTraceNorm Z / (1 - ‖Z‖) := by
  have h_eig (i : ι) : |hZ.eigenvalues i| ≤ ‖Z‖ := by
    simpa only [Real.norm_eq_abs] using
      IsometricContinuousFunctionalCalculus.norm_spectrum_le Z
        (hZ.eigenvalues_mem_spectrum_real i) hZ.isSelfAdjoint
  have hpos (i : ι) : 0 < 1 - hZ.eigenvalues i := by
    linarith [le_abs_self (hZ.eigenvalues i), h_eig i]
  rw [← matrix_one_sub_cfc hZ, matrix_det_cfc hZ,
    Real.log_prod (fun i _ => (hpos i).ne'), matrixTraceNorm_eq_sum_abs_eigenvalues hZ,
    Finset.sum_div]
  calc
    |∑ i, Real.log (1 - hZ.eigenvalues i)| ≤
        ∑ i, |Real.log (1 - hZ.eigenvalues i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => real_log_one_sub_bound hδ (h_eig i)

theorem abs_trace_log_one_sub_le {Z : Matrix ι ι ℝ}
    (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) :
    |(cfc Real.log (1 - Z)).trace| ≤ matrixTraceNorm Z / (1 - ‖Z‖) := by
  rw [matrix_trace_log_eq_log_det (matrix_one_sub_posDef_of_norm_lt_one hZ hδ)]
  exact abs_log_det_one_sub_le hZ hδ

end VacuumBellSeparation.Gaussian
