/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FinitePowerTraceHolder

/-!
# Actual strip bounds for finite spectral complex powers

Imaginary powers are unitary, so the norm depends only on the real part
of the exponent. Compact real intervals therefore give uniform bounds
on complete vertical strips. A separate genuine trace-norm endpoint
bounds Tr(A^z U) by Tr(A^(Re z)).
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Set
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_trace_positive_rpow {A : Matrix ι ι ℂ} (hA : A.PosDef) (p : ℝ) :
    (A ^ p).trace = (∑ i, hA.isHermitian.eigenvalues i ^ p : ℝ) := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, hA.isHermitian.cfc_eq,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sum]

theorem real_trace_positive_rpow_nonneg {A : Matrix ι ι ℂ} (hA : A.PosDef) (p : ℝ) :
    0 ≤ (A ^ p).trace.re := by
  rw [complex_trace_positive_rpow hA p, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hA.eigenvalues_pos i).le p

theorem norm_unitary_entry_le_one (U : unitary (Matrix ι ι ℂ)) (i j : ι) :
    ‖(U : Matrix ι ι ℂ) i j‖ ≤ 1 := by
  have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    unitaryOverlapWeight_nonneg U i k) (Finset.mem_univ j)
  rw [sum_unitaryOverlapWeight_row] at hs
  dsimp only [unitaryOverlapWeight] at hs
  nlinarith [norm_nonneg ((U : Matrix ι ι ℂ) i j)]

theorem norm_trace_diagonal_mul_unitary_le (U : unitary (Matrix ι ι ℂ)) (a : ι → ℂ) :
    ‖(Matrix.diagonal a * (U : Matrix ι ι ℂ)).trace‖ ≤ ∑ i, ‖a i‖ := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_unitary_entry_le_one U i i)
    (norm_nonneg _)

theorem norm_trace_complexPower_mul_unitary_le {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (z : ℂ) (U : unitary (Matrix ι ι ℂ)) :
    ‖(positiveMatrixComplexPower hA z * (U : Matrix ι ι ℂ)).trace‖ ≤ (A ^ z.re).trace.re := by
  let W := hA.isHermitian.eigenvectorUnitary
  let a : ι → ℂ := fun i => Complex.exp (z * (Real.log (hA.isHermitian.eigenvalues i) : ℂ))
  have he : (positiveMatrixComplexPower hA z * (U : Matrix ι ι ℂ)).trace =
      (Matrix.diagonal a * ((star W * U * W : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)).trace := by
    change (((W : Matrix ι ι ℂ) * Matrix.diagonal a * star (W : Matrix ι ι ℂ)) *
      (U : Matrix ι ι ℂ)).trace = _
    simp only [Submonoid.coe_mul, Unitary.coe_star]
    calc
      _ = ((W : Matrix ι ι ℂ) * (Matrix.diagonal a * (star (W : Matrix ι ι ℂ) *
        (U : Matrix ι ι ℂ)))).trace := by
        congr 1
        noncomm_ring
      _ = _ := by rw [Matrix.trace_mul_comm]; congr 1; noncomm_ring
  rw [he, complex_trace_positive_rpow hA z.re, Complex.ofReal_re]
  have h := norm_trace_diagonal_mul_unitary_le (star W * U * W) a
  simpa only [a, norm_positiveMatrixComplexPower_eigenvalue hA z] using h

theorem norm_trace_positive_mul_unitary_le {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (U : unitary (Matrix ι ι ℂ)) : ‖(A * (U : Matrix ι ι ℂ)).trace‖ ≤ A.trace.re := by
  simpa only [positiveMatrixComplexPower_one, Complex.one_re,
    CFC.rpow_one A hA.posSemidef.nonneg] using
    norm_trace_complexPower_mul_unitary_le hA 1 U

theorem norm_positiveMatrixComplexPower_re {A : Matrix ι ι ℂ} (hA : A.PosDef) (z : ℂ) :
    ‖positiveMatrixComplexPower hA z‖ = ‖positiveMatrixComplexPower hA (z.re : ℂ)‖ := by
  rw [positiveMatrixComplexPower_split, CStarRing.norm_mul_coe_unitary,
    positiveMatrixComplexPower_real]

theorem exists_bound_positiveMatrixComplexPower_strip {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖positiveMatrixComplexPower hA z‖ ≤ C := by
  have hc : Continuous (fun t : ℝ => ‖positiveMatrixComplexPower hA (t : ℂ)‖) :=
    ((differentiable_positiveMatrixComplexPower hA).continuous.comp Complex.continuous_ofReal).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  rw [norm_positiveMatrixComplexPower_re]
  exact (hC ⟨z.re, hz, rfl⟩).trans (le_max_left _ _)

theorem exists_bound_positiveMatrixComplexPower_real_mul_strip {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc 0 1 →
      ‖positiveMatrixComplexPower hA ((c : ℂ) * z)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_bound_positiveMatrixComplexPower_strip hA (min 0 c) (max 0 c)
  refine ⟨C, hC, ?_⟩
  intro z hz
  apply hb
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hc : 0 ≤ c
  · rw [min_eq_left hc, max_eq_right hc]
    exact ⟨mul_nonneg hc hz.1, by nlinarith [hz.2]⟩
  · have hc' := le_of_lt (lt_of_not_ge hc)
    rw [min_eq_right hc', max_eq_left hc']
    exact ⟨by nlinarith [hz.2], mul_nonpos_of_nonpos_of_nonneg hc' hz.1⟩

end VacuumBellSeparation.Gaussian
