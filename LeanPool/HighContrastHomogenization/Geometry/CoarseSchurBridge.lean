/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Setup.ResponsePositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu

/-!
# High-contrast homogenization: Geometry.CoarseSchurBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Schur blocks of the coarse response, and their ordering

The variational coarse block `𝐀(U; a)` of `s.introduction` is carried here as a
`BlockMat d` over a plain subset of `ℝ^d` and a field of the
coefficient space, and its Schur data is read off the four corners by
`schurSigma` and `schurSigmaStar`.  CoarseGraining's chapter 2 carries the same
object over a nonempty bounded open convex domain and a coefficient object with
its own ellipticity data, and names the same two matrices `sigmaCoarse` and
`sigmaStarCoarse`, extracted from the response functional rather than from the
corners.  The ordering `σ_* ≤ σ` is proved there.

This file identifies the two readings, so that the ordering becomes available on
the response of a field of the coefficient space.

Three steps.  A field of the coefficient space is uniformly elliptic almost
everywhere on all of `ℝ^d`, so it is a coefficient object on every domain, with
the *same* representative: this is `CoeffSpace.coeffOn`.  The two block matrices
then agree, because both are characterized by the same quadratic identity
`μ(U, P; a) = ½ P · 𝐀 P` for every doubled vector `P`, and that identity
determines the matrix.  Finally, on the assembled form
`𝐀 = (b, -kᵗ σ_*⁻¹; -σ_*⁻¹ k, σ_*⁻¹)` the corner formulas are algebra: inverting
the lower-right corner returns `σ_*`, the Schur skew block is `k` once `σ_*⁻¹`
is invertible, and the correction `kᵗ σ_*⁻¹ k` subtracted from `b` returns `σ`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## A field of the coefficient space as a coefficient object on a domain -/

/-- The ellipticity constants a field of the coefficient space carries on a
bounded open convex domain. -/
theorem CoeffSpace.exists_ellipticity_on_domain (a : CoeffSpace d)
    (U : Book.Ch02.Domain d) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ᵐ x ∂volume, x ∈ (U : Set (Vec d)) →
        IsEllipticMatrix lam Lam ((⇑a.1 : CoeffField d) x) :=
  a.2.exists_ae_isEllipticMatrix_of_isBounded U.isDomain.isBoundedDomain.isBounded

/-- A field of the coefficient space, viewed as a coefficient object on a
nonempty bounded open convex domain: the ellipticity constants are the ones the
field carries on that domain, and the representative is unchanged. -/
@[expose]
def CoeffSpace.coeffOn (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    Book.Ch02.CoeffOn U where
  toCoeffField := ⇑a.1
  lam := (a.exists_ellipticity_on_domain U).choose
  Lam := (a.exists_ellipticity_on_domain U).choose_spec.choose
  lam_pos := (a.exists_ellipticity_on_domain U).choose_spec.choose_spec.1
  lam_le_Lam := (a.exists_ellipticity_on_domain U).choose_spec.choose_spec.2.1
  aeStronglyMeasurable := by
    intro i j
    have hbase : AEStronglyMeasurable (fun x : Vec d => (⇑a.1 : Vec d → Mat d) x i j)
        volume :=
      (continuous_id.matrix_elem i j).comp_aestronglyMeasurable a.1.aestronglyMeasurable
    refine (hbase.restrict (s := (U : Set (Vec d)))).congr ?_
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    simp [restrictCoeffField, hx]
  aeElliptic := by
    filter_upwards
      [ae_restrict_of_ae
        (a.exists_ellipticity_on_domain U).choose_spec.choose_spec.2.2,
        ae_restrict_mem U.measurableSet] with x hx hxU
    exact hx hxU

@[simp] theorem CoeffSpace.coeffOn_toCoeffField (a : CoeffSpace d)
    (U : Book.Ch02.Domain d) : (a.coeffOn U).toCoeffField = ⇑a.1 := rfl

/-! ## The two readings of the coarse block agree -/

/-- **The coarse response is the chapter 2 coarse block matrix.**  Both are
determined by the same quadratic identity for the variational quantity. -/
theorem coarseBlock_eq_coarseBlockMatrix (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    coarseBlock (U : Set (Vec d)) a = Book.Ch02.coarseBlockMatrix U (a.coeffOn U) := by
  refine (eq_coarseBlockMatrix_of_isCoarseBlockMatrix ?_).symm
  refine ⟨Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U (a.coeffOn U), fun P => ?_⟩
  have hmu : Book.Ch02.doubledMu U (a.coeffOn U) P = Mu (U : Set (Vec d)) P ⇑a.1 :=
    Book.Ch02.doubledMu_eq_Mu U (a.coeffOn U) P
  have hquad := (Book.Ch02.doubledMuTheory U (a.coeffOn U)).mu_quadratic P
  rw [← hmu, hquad]

/-! ## Positivity on general domains -/

/-- The coarse response of a field of the coefficient space is positive definite
on every bounded open convex nonempty domain: it is the chapter 2 coarse block
matrix of the field read as a coefficient object on that domain. -/
theorem blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock U a) := by
  have h := (Book.Ch02.blockCoarseMatrixTheory (Book.Ch02.Domain.mk U hU hne)
    (a.coeffOn (Book.Ch02.Domain.mk U hU hne))).block_matrix_posDef
  rwa [← coarseBlock_eq_coarseBlockMatrix a (Book.Ch02.Domain.mk U hU hne)] at h

/-! ## The corner formulas -/

/-- The Schur skew block of the assembled block is `k`. -/
theorem schurSkew_blockMatrixOfCoarseMatrices {M : Book.Ch02.CoarseMatrices d}
    (hdet : IsUnit M.sigmaStarInv.det) :
    schurSkew (Book.Ch02.blockMatrixOfCoarseMatrices M) = M.kappa := by
  change -(M.sigmaStarInv⁻¹ * -(M.sigmaStarInv * M.kappa)) = M.kappa
  rw [Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
    Matrix.one_mul]

/-- The Schur symmetric block of the assembled block is `σ`: the correction
`kᵗ σ_*⁻¹ k` is exactly what `b` adds to `σ`. -/
theorem schurSigma_blockMatrixOfCoarseMatrices {M : Book.Ch02.CoarseMatrices d}
    (hdet : IsUnit M.sigmaStarInv.det) :
    schurSigma (Book.Ch02.blockMatrixOfCoarseMatrices M) = M.sigma := by
  rw [schurSigma, schurSkew_blockMatrixOfCoarseMatrices hdet]
  change M.sigma + matTranspose M.kappa * M.sigmaStarInv * M.kappa
      - matTranspose M.kappa * M.sigmaStarInv * M.kappa = M.sigma
  abel

/-! ## The Schur data of the coarse response -/

/-- The Schur block `σ_*` of the coarse response is the chapter 2 matrix
`sigmaStarCoarse`. -/
theorem schurSigmaStar_coarseBlock (a : CoeffSpace d) (U : Book.Ch02.Domain d) :
    schurSigmaStar (coarseBlock (U : Set (Vec d)) a)
      = Book.Ch02.sigmaStarCoarse U (a.coeffOn U) := by
  rw [schurSigmaStar, coarseBlock_eq_coarseBlockMatrix a U]
  rfl

/-- The Schur block `σ` of the coarse response is the chapter 2 matrix
`sigmaCoarse`. -/
theorem schurSigma_coarseBlock (a : CoeffSpace d) (U : Book.Ch02.Domain d)
    (hpos : Book.Ch02.BlockPosDef (coarseBlock (U : Set (Vec d)) a)) :
    schurSigma (coarseBlock (U : Set (Vec d)) a)
      = Book.Ch02.sigmaCoarse U (a.coeffOn U) := by
  have hdet : IsUnit (Book.Ch02.sigmaStarInvCoarse U (a.coeffOn U)).det := by
    have h := isUnit_det_lowerRight hpos
    rwa [coarseBlock_eq_coarseBlockMatrix a U] at h
  rw [coarseBlock_eq_coarseBlockMatrix a U]
  exact schurSigma_blockMatrixOfCoarseMatrices
    (M := Book.Ch02.coarseMatrices U (a.coeffOn U)) hdet

/-! ## The ordering -/

/-- **The Schur blocks of the coarse response are ordered**, `σ_* ≤ σ`, on every
nonempty bounded open convex domain and at every field of the coefficient
space. -/
theorem matLoewnerLE_schurSigmaStar_schurSigma_coarseBlock (a : CoeffSpace d)
    (U : Book.Ch02.Domain d)
    (hpos : Book.Ch02.BlockPosDef (coarseBlock (U : Set (Vec d)) a)) :
    MatLoewnerLE (schurSigmaStar (coarseBlock (U : Set (Vec d)) a))
      (schurSigma (coarseBlock (U : Set (Vec d)) a)) := by
  rw [schurSigmaStar_coarseBlock a U, schurSigma_coarseBlock a U hpos]
  exact Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U (a.coeffOn U)

/-- The centered triadic cube `□_m` of `s.introduction` as a nonempty bounded
open convex domain. -/
theorem cubeDomain_originCube_coe (m : ℤ) :
    (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) = centeredCube d m := rfl

/-- The Schur blocks of the coarse response of a centered triadic cube are
ordered, at every field of the coefficient space. -/
theorem matLoewnerLE_schurSigmaStar_schurSigma_coarseBlock_centeredCube [NeZero d]
    (m : ℤ) (a : CoeffSpace d) :
    MatLoewnerLE (schurSigmaStar (coarseBlock (centeredCube d m) a))
      (schurSigma (coarseBlock (centeredCube d m) a)) :=
  matLoewnerLE_schurSigmaStar_schurSigma_coarseBlock a
    (Book.Ch02.cubeDomain (originCube d m)) (blockPosDef_coarseBlock m a)

/-- **The aspect ratio of a realized coarse block is at least one.**  The Schur
ordering holds on the coarse response of a centered triadic cube, so the bound
of `e.reference.aspect.ratio` applies to it with no further hypothesis. -/
theorem one_le_aspectRatio_coarseBlock_centeredCube [NeZero d] (m : ℤ)
    (a : CoeffSpace d) : 1 ≤ aspectRatio (coarseBlock (centeredCube d m) a) :=
  one_le_aspectRatio_of_schurSigmaStar_le
    (isSymmetricBlockMat_coarseBlockMatrix (centeredCube d m) ⇑a.1)
    (blockPosDef_coarseBlock m a)
    (matLoewnerLE_schurSigmaStar_schurSigma_coarseBlock_centeredCube m a)

end

end HighContrast
end HCPolySupport
