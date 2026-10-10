/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Symplectic
public import Mathlib.Data.Matrix.Mul

/-!
Coordinate matrices for the symplectic form. The matrix identity uses ordinary transpose,
rather than conjugate transpose, and the same (p, q) coordinate order.
-/

@[expose] public section

noncomputable section

namespace KamProject.Arnold1963

theorem symplecticMatrix_eq_neg_mathlibJ (n : ℕ) :
    symplecticMatrix n = -Matrix.J (Fin n) ℂ := rfl

theorem symplectic_matrix_identity_iff_mathlib {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    M.transpose * symplecticMatrix n * M = symplecticMatrix n ↔
      M.transpose * Matrix.J (Fin n) ℂ * M = Matrix.J (Fin n) ℂ := by
  simp only [symplecticMatrix, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- The unified coordinate function of a phase vector. -/
def phaseCoordinate {n : ℕ} (v : ComplexPhaseSpace n) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim v.1 v.2

/-- The matrix of a linear phase transformation in the unified coordinate basis. -/
def phaseLinearMatrix {n : ℕ} (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fun i j => phaseCoordinate (A (phaseDirection j)) i

theorem phaseLinearMatrix_symplectic_apply {n : ℕ}
    (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) (i j : Fin n ⊕ Fin n) :
    ((phaseLinearMatrix A).transpose * symplecticMatrix n * phaseLinearMatrix A) i j =
      symplecticForm (A (phaseDirection i)) (A (phaseDirection j)) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply,
    phaseLinearMatrix, phaseCoordinate, Finset.sum_add_distrib, symplecticForm,
    neg_mul, sub_eq_add_neg, add_comm]

theorem IsSymplecticLinear.matrix_identity {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    (phaseLinearMatrix A).transpose * symplecticMatrix n * phaseLinearMatrix A =
      symplecticMatrix n := by
  ext i j
  rw [phaseLinearMatrix_symplectic_apply, hA]
  exact (symplecticMatrix_apply i j).symm

end KamProject.Arnold1963
