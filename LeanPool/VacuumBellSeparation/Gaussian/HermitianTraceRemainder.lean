/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryEigenbasisOverlap

/-!
# An exact spectral trace remainder without eigenvalue derivatives

The change-of-eigenbasis unitary is constructed from the actual spectral
bases of two Hermitian matrices. Its nonnegative overlap weights give an
exact scalar remainder formula for the actual CFC trace. Repeated
eigenvalues require no choice of differentiable eigenvalue branches.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change of coordinates between two orthonormal eigenbases. -/
def eigenbasisOverlapUnitary {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : unitary (Matrix ι ι ℂ) :=
  star hA.eigenvectorUnitary * hB.eigenvectorUnitary

theorem real_matrix_trace_cfc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp only [Complex.re_sum, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re]

omit [DecidableEq ι] in
theorem trace_conjugated_product (P Q X Y : Matrix ι ι ℂ) :
    ((P * X * Pᴴ) * (Q * Y * Qᴴ)).trace =
      (X * ((Pᴴ * Q) * Y * (Pᴴ * Q)ᴴ)).trace := by
  calc
    _ = (P * (X * Pᴴ * Q * Y * Qᴴ)).trace := congrArg Matrix.trace (by noncomm_ring)
    _ = ((X * Pᴴ * Q * Y * Qᴴ) * P).trace := Matrix.trace_mul_comm _ _
    _ = _ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      congr 1
      noncomm_ring

theorem real_trace_cfc_mul_cfc {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace.re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j := by
  rw [hA.cfc_eq, hB.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose]
  rw [trace_conjugated_product]
  exact real_trace_mixed_unitary_diagonals (eigenbasisOverlapUnitary hA hB)
    (f ∘ hA.eigenvalues) (g ∘ hB.eigenvalues)

theorem unitaryOverlapWeight_same_eigenbasis {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i j : ι) :
    unitaryOverlapWeight (eigenbasisOverlapUnitary hA hA) i j = if i = j then 1 else 0 := by
  by_cases hij : i = j <;>
    simp [eigenbasisOverlapUnitary, unitaryOverlapWeight, hij]

theorem real_trace_cfc_mul_self {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A * A).trace.re = ∑ i, f (hA.eigenvalues i) * hA.eigenvalues i := by
  have h := real_trace_cfc_mul_cfc hA hA f id
  rw [cfc_id ℝ A hA.isSelfAdjoint] at h
  simpa only [unitaryOverlapWeight_same_eigenbasis, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, id_eq] using h

theorem unitary_weighted_scalar_remainder (U : unitary (Matrix ι ι ℂ))
    (a b : ι → ℝ) (f d : ℝ → ℝ) :
    (∑ j, f (b j)) - (∑ i, f (a i)) -
      ((∑ i, ∑ j, d (a i) * b j * unitaryOverlapWeight U i j) -
        ∑ i, d (a i) * a i) =
      ∑ i, ∑ j, unitaryOverlapWeight U i j *
        (f (b j) - f (a i) - d (a i) * (b j - a i)) := by
  have hreorder : (∑ i, ∑ j, unitaryOverlapWeight U i j * d (a i) * b j) =
      ∑ i, ∑ j, d (a i) * b j * unitaryOverlapWeight U i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hleft : (∑ i, ∑ j, unitaryOverlapWeight U i j * d (a i) * a i) =
      ∑ i, d (a i) * a i := by
    simpa only [mul_assoc] using unitaryOverlapWeight_sum_left U (fun i => d (a i) * a i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
  rw [unitaryOverlapWeight_sum_right, unitaryOverlapWeight_sum_left, hreorder, hleft]

/-- The exact actual-CFC trace remainder, valid with arbitrary repeated
eigenvalues and arbitrary scalar functions on the finite spectra. -/
theorem real_trace_cfc_remainder {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f d : ℝ → ℝ) :
    (cfc f B - cfc f A - cfc d A * (B - A)).trace.re =
      ∑ i, ∑ j, unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (f (hB.eigenvalues j) - f (hA.eigenvalues i) -
          d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)) := by
  have hcross := real_trace_cfc_mul_cfc hA hB d id
  rw [cfc_id ℝ B hB.isSelfAdjoint] at hcross
  simp only [id_eq] at hcross
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Complex.sub_re, Complex.sub_re, Complex.sub_re,
    real_matrix_trace_cfc hA, real_matrix_trace_cfc hB,
    hcross, real_trace_cfc_mul_self hA]
  exact unitary_weighted_scalar_remainder (eigenbasisOverlapUnitary hA hB)
    hA.eigenvalues hB.eigenvalues f d

theorem abs_real_trace_cfc_remainder_le {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f d : ℝ → ℝ) (C : ℝ)
    (hrem : ∀ i j, |f (hB.eigenvalues j) - f (hA.eigenvalues i) -
      d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i)| ≤
        C * (hB.eigenvalues j - hA.eigenvalues i) ^ 2) :
    |(cfc f B - cfc f A - cfc d A * (B - A)).trace.re| ≤
      C * ∑ i, ∑ j, unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (hB.eigenvalues j - hA.eigenvalues i) ^ 2 := by
  rw [real_trace_cfc_remainder hA hB f d]
  calc
    _ ≤ ∑ i, |∑ j, unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (f (hB.eigenvalues j) - f (hA.eigenvalues i) -
          d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (f (hB.eigenvalues j) - f (hA.eigenvalues i) -
          d (hA.eigenvalues i) * (hB.eigenvalues j - hA.eigenvalues i))| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, unitaryOverlapWeight (eigenbasisOverlapUnitary hA hB) i j *
        (C * (hB.eigenvalues j - hA.eigenvalues i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (unitaryOverlapWeight_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left (hrem i j) (unitaryOverlapWeight_nonneg _ _ _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end VacuumBellSeparation.Gaussian
