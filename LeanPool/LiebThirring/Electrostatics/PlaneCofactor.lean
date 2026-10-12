/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.PlaneProjection

/-!
# The normal component of the planar projection Jacobian

Deleting one row and the last column of an orthogonal matrix gives an absolute minor equal to
the corresponding last-column entry.

The two unit direction vectors of an orthonormal affine frame.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped Matrix

namespace LiebThirring

/-- Deleting one row and the last column of an orthogonal matrix gives an absolute
minor equal to the corresponding last-column entry. -/
theorem abs_det_minor_eq_abs_last_column
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Qᵀ * Q = 1) (a : Fin 3) :
    |(Q.submatrix a.succAbove (2 : Fin 3).succAbove).det| = |Q a 2| := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hadj : Q.adjugate = Q.det • Qᵀ := by
    calc
      Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQQ, mul_one]
      _ = (Q.adjugate * Q) * Qᵀ := (mul_assoc _ _ _).symm
      _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  have hdet : |Q.det| = 1 := by
    have hd := congrArg Matrix.det hQ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hdabs : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, hd, abs_one]
    nlinarith only [hdabs, abs_nonneg Q.det]
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 a) hadj
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul] at he
  have heabs := congrArg abs he
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hdet] using heabs

/-- The two unit direction vectors of an orthonormal affine frame. -/
noncomputable def planeFrameVector (n b : Position)
    (F : PlaneFrame (affinePlane n b)) (i : Fin 2) : Position :=
  F.linearIsometryEquiv (EuclideanSpace.basisFun (Fin 2) ℝ i)

/-- The frame direction vectors are orthonormal. -/
theorem inner_planeFrameVector (n b : Position) (F : PlaneFrame (affinePlane n b))
    (i j : Fin 2) : inner ℝ (planeFrameVector n b F i) (planeFrameVector n b F j) =
      if i = j then 1 else 0 := by
  change inner ℝ (F.linearIsometryEquiv (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (F.linearIsometryEquiv (EuclideanSpace.basisFun (Fin 2) ℝ j)) = _
  rw [F.linearIsometryEquiv.inner_map_map, OrthonormalBasis.inner_eq_ite]

/-- The frame direction vectors are perpendicular to the given normal. -/
theorem inner_normal_planeFrameVector (n b : Position) (F : PlaneFrame (affinePlane n b))
    (i : Fin 2) : inner ℝ n (planeFrameVector n b F i) = 0 := by
  have hi := (F.linearIsometryEquiv (EuclideanSpace.basisFun (Fin 2) ℝ i)).property
  change planeFrameVector n b F i ∈ (AffineSubspace.mk' b (ℝ ∙ n)ᗮ).direction at hi
  rw [AffineSubspace.direction_mk'] at hi
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hi

/-- Columns of the affine frame's linear part, followed by the normal. -/
noncomputable def planeFrameMatrix (n b : Position)
    (F : PlaneFrame (affinePlane n b)) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (![planeFrameVector n b F 0, planeFrameVector n b F 1, n] j) i

/-- The completed frame columns are orthonormal when its normal has unit norm. -/
theorem planeFrameMatrix_inner_columns (n b : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (i j : Fin 3) :
    inner ℝ (![planeFrameVector n b F 0, planeFrameVector n b F 1, n] i)
      (![planeFrameVector n b F 0, planeFrameVector n b F 1, n] j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j
  · exact inner_planeFrameVector n b F 0 0
  · exact inner_planeFrameVector n b F 0 1
  · exact (real_inner_comm _ _).trans (inner_normal_planeFrameVector n b F 0)
  · exact inner_planeFrameVector n b F 1 0
  · exact inner_planeFrameVector n b F 1 1
  · exact (real_inner_comm _ _).trans (inner_normal_planeFrameVector n b F 1)
  · exact inner_normal_planeFrameVector n b F 0
  · exact inner_normal_planeFrameVector n b F 1
  · change inner ℝ n n = 1
    rw [real_inner_self_eq_norm_sq, hn, one_pow]

/-- The completed frame matrix is orthogonal when its normal has unit norm. -/
theorem planeFrameMatrix_transpose_mul (n b : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) :
    (planeFrameMatrix n b F)ᵀ * planeFrameMatrix n b F = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ k : Fin 3,
    (![planeFrameVector n b F 0, planeFrameVector n b F 1, n] i) k *
    (![planeFrameVector n b F 0, planeFrameVector n b F 1, n] j) k) = _
  rw [← planeFrameMatrix_inner_columns n b hn F i j, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

/-- The projection chart's matrix is the corresponding minor of the completed frame. -/
theorem planeProjectionChart_toMatrix (n b : Position) (a : Fin 3) (ha : n a ≠ 0)
    (F : PlaneFrame (affinePlane n b)) :
    LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 2)) (PiLp.basisFun 2 ℝ (Fin 2))
      ((planeProjectionChart n b a ha F).linear : Planar →ₗ[ℝ] Planar) =
      (planeFrameMatrix n b F).submatrix a.succAbove (2 : Fin 3).succAbove := by
  ext i j
  rw [LinearMap.toMatrix_apply, PiLp.basisFun_repr]
  fin_cases j <;> rfl

/-- The absolute area Jacobian of coordinate deletion is the absolute normal component. -/
theorem abs_det_planeProjectionChart (n b : Position) (hn : ‖n‖ = 1)
    (a : Fin 3) (ha : n a ≠ 0) (F : PlaneFrame (affinePlane n b)) :
    |LinearMap.det ((planeProjectionChart n b a ha F).linear : Planar →ₗ[ℝ] Planar)| =
      |n a| := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)),
    planeProjectionChart_toMatrix]
  exact abs_det_minor_eq_abs_last_column _ (planeFrameMatrix_transpose_mul n b hn F) a

end LiebThirring

end
