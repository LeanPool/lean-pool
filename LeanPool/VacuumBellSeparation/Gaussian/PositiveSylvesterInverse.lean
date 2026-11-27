/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNorm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Star

/-!
# The actual inverse of the positive Sylvester derivative

At a strictly positive real symmetric R, the linear map X ↦ RX+XR
is inverted in a fixed actual eigenbasis by division by λᵢ+λⱼ.
Its restriction to the genuine self-adjoint real subspace is an actual
continuous linear equivalence, valid also at repeated eigenvalues.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal Sylvester equivalence. -/
def diagonalSylvesterEquiv (d : ι → ℝ) (hd : ∀ i j, d i + d j ≠ 0) :
    Matrix ι ι ℝ ≃ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := Matrix.diagonal d * X + X * Matrix.diagonal d
  invFun Y := fun i j => Y i j / (d i + d j)
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]
  left_inv X := by
    ext i j
    change ((Matrix.diagonal d * X + X * Matrix.diagonal d) i j) / (d i + d j) = X i j
    rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    field_simp [hd i j]
  right_inv Y := by
    ext i j
    change (Matrix.diagonal d * (Matrix.of (fun i j => Y i j / (d i + d j))) +
      (Matrix.of (fun i j => Y i j / (d i + d j))) * Matrix.diagonal d) i j = Y i j
    rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    change d i * (Y i j / (d i + d j)) + (Y i j / (d i + d j)) * d j = Y i j
    field_simp [hd i j]

/-- Invertible Sylvester map obtained by adding left and right multiplication by a positive
matrix. -/
def positiveSylvesterEquiv {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    Matrix ι ι ℝ ≃ₗ[ℝ] Matrix ι ι ℝ :=
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hR.isHermitian.eigenvectorUnitary
  C.symm.toAlgEquiv.toLinearEquiv.trans
    ((diagonalSylvesterEquiv hR.isHermitian.eigenvalues
      (fun i j => (add_pos (hR.eigenvalues_pos i) (hR.eigenvalues_pos j)).ne')).trans
        C.toAlgEquiv.toLinearEquiv)

theorem positiveSylvesterEquiv_apply {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (X : Matrix ι ι ℝ) : positiveSylvesterEquiv hR X = R * X + X * R := by
  let C := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hR.isHermitian.eigenvectorUnitary
  have hspec : C (Matrix.diagonal hR.isHermitian.eigenvalues) = R := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using
      hR.isHermitian.spectral_theorem.symm
  change C (Matrix.diagonal hR.isHermitian.eigenvalues * C.symm X +
    C.symm X * Matrix.diagonal hR.isHermitian.eigenvalues) = _
  rw [map_add, map_mul, map_mul, C.apply_symm_apply, hspec]

theorem positiveSylvesterEquiv_star {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (X : Matrix ι ι ℝ) : positiveSylvesterEquiv hR (star X) =
      star (positiveSylvesterEquiv hR X) := by
  rw [positiveSylvesterEquiv_apply, positiveSylvesterEquiv_apply, star_add, star_mul, star_mul,
    hR.isHermitian.isSelfAdjoint.star_eq]
  exact add_comm _ _

/-- Real symmetric matrix space with underlying type `selfAdjoint.submodule ℝ (Matrix ι ι ℝ)`. -/
abbrev RealSymmetricMatrixSpace (ι : Type*) :=
  selfAdjoint.submodule ℝ (Matrix ι ι ℝ)

omit [DecidableEq ι] [Fintype ι] in
theorem realSymmetricMatrix_isHermitian (X : RealSymmetricMatrixSpace ι) :
    (X : Matrix ι ι ℝ).IsHermitian := X.property

theorem positiveSylvesterEquiv_preserves_selfAdjoint {R X : Matrix ι ι ℝ}
    (hR : R.PosDef) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (positiveSylvesterEquiv hR X) := by
  change star (positiveSylvesterEquiv hR X) = _
  rw [← positiveSylvesterEquiv_star, hX.star_eq]

theorem positiveSylvesterEquiv_symm_preserves_selfAdjoint {R Y : Matrix ι ι ℝ}
    (hR : R.PosDef) (hY : IsSelfAdjoint Y) :
    IsSelfAdjoint ((positiveSylvesterEquiv hR).symm Y) := by
  change star ((positiveSylvesterEquiv hR).symm Y) = _
  apply (positiveSylvesterEquiv hR).injective
  rw [positiveSylvesterEquiv_star, LinearEquiv.apply_symm_apply, hY.star_eq]

/-- Positive Sylvester self adjoint equivalence of type `RealSymmetricMatrixSpace ι ≃ₗ[ℝ]
RealSymmetricMatrixSpace ι where toFun X`. -/
def positiveSylvesterSelfAdjointEquiv {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    RealSymmetricMatrixSpace ι ≃ₗ[ℝ] RealSymmetricMatrixSpace ι where
  toFun X := ⟨positiveSylvesterEquiv hR X,
    positiveSylvesterEquiv_preserves_selfAdjoint hR X.property⟩
  invFun Y := ⟨(positiveSylvesterEquiv hR).symm Y,
    positiveSylvesterEquiv_symm_preserves_selfAdjoint hR Y.property⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add (positiveSylvesterEquiv hR) (X : Matrix ι ι ℝ) (Y : Matrix ι ι ℝ)
  map_smul' c X := by
    apply Subtype.ext
    exact map_smul (positiveSylvesterEquiv hR) c (X : Matrix ι ι ℝ)
  left_inv X := by
    apply Subtype.ext
    exact (positiveSylvesterEquiv hR).left_inv X
  right_inv Y := by
    apply Subtype.ext
    exact (positiveSylvesterEquiv hR).right_inv Y

/-- Positive Sylvester self adjoint continuous equivalence of type `RealSymmetricMatrixSpace ι
≃L[ℝ] RealSymmetricMatrixSpace ι`. -/
def positiveSylvesterSelfAdjointContinuousEquiv {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    RealSymmetricMatrixSpace ι ≃L[ℝ] RealSymmetricMatrixSpace ι :=
  (positiveSylvesterSelfAdjointEquiv hR).toContinuousLinearEquiv

@[simp] theorem positiveSylvesterSelfAdjointContinuousEquiv_apply
    {R : Matrix ι ι ℝ} (hR : R.PosDef) (X : RealSymmetricMatrixSpace ι) :
    ((positiveSylvesterSelfAdjointContinuousEquiv hR X : RealSymmetricMatrixSpace ι) :
      Matrix ι ι ℝ) = R * (X : Matrix ι ι ℝ) + (X : Matrix ι ι ℝ) * R :=
  positiveSylvesterEquiv_apply hR X

theorem positiveSylvester_inverse_solves {R : Matrix ι ι ℝ} (hR : R.PosDef)
    (Y : RealSymmetricMatrixSpace ι) :
    R * ((positiveSylvesterSelfAdjointContinuousEquiv hR).symm Y : Matrix ι ι ℝ) +
      ((positiveSylvesterSelfAdjointContinuousEquiv hR).symm Y : Matrix ι ι ℝ) * R =
        (Y : Matrix ι ι ℝ) := by
  have h := positiveSylvesterSelfAdjointContinuousEquiv_apply hR
    ((positiveSylvesterSelfAdjointContinuousEquiv hR).symm Y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

end VacuumBellSeparation.Gaussian
