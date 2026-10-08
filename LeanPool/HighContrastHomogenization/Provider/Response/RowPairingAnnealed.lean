/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.AlignedIdentities
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.QuadraticStability.CauchySchwarz

/-!
# High-contrast homogenization: Provider.Response.RowPairingAnnealed

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cell pairing of a cutoff-defect mean row

Pairing a coarse-grained cell average against a fixed load is a Cauchy-Schwarz
step for the starred coarse block: the energy map bounds the starred quadratic
form of the cell average by the cell energy, and the load contributes the
quadratic form of the starred inverse.  The starred inverse is the reflection of
the response block, so the load's contribution is read off the response block's
opposite diagonal entry -- the gradient slot pairs with the lower-right block and
the flux slot with the upper-left block.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Symmetry of the starred coarse block -/

private theorem isSymm_toFullBlockMat_of_isSymmetricBlockMat {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) : (toFullBlockMat A).IsSymm := by
  funext α β
  have h := hA β α
  cases α <;> cases β <;> exact h

/-- **The starred coarse block is symmetric.**  Its inverse is the reflection of
the response block, reflection preserves block symmetry, and matrix inversion
preserves symmetry. -/
theorem isSymmetricBlockMat_coarseStarredBlockMatrix {U : Domain d}
    (c : CoeffOn U) :
    IsSymmetricBlockMat (Book.Ch02.coarseStarredBlockMatrix U c) := by
  have hbase : IsSymmetricBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c) := by
    rw [(Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_inverse_formula]
    exact isSymmetricBlockMat_blockReflect
      (Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U c)
  have hfull : (toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c)).IsSymm :=
    isSymm_toFullBlockMat_of_isSymmetricBlockMat hbase
  have hfullEq :
      Matrix.transpose
          (toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c)) =
        toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c) := hfull
  have hinv :
      ((toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c))⁻¹).IsSymm := by
    change Matrix.transpose
        ((toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c))⁻¹) = _
    rw [Matrix.transpose_nonsing_inv, hfullEq]
  change IsSymmetricBlockMat
    (ofFullBlockMat ((toFullBlockMat (Book.Ch02.coarseStarredBlockMatrixInv U c))⁻¹))
  exact isSymmetricBlockMat_of_isSymm hinv

/-! ## Pairing against an inverse block form -/

private theorem blockVecDot_pair_inl (y : BlockVec d) (x : Vec d) :
    blockVecDot y ((x, 0) : BlockVec d) = vecDot y.1 x := by
  change vecDot y.1 x + vecDot y.2 0 = _
  rw [vecDot_zero_right, add_zero]

private theorem blockVecDot_pair_inr (y : BlockVec d) (x : Vec d) :
    blockVecDot y ((0, x) : BlockVec d) = vecDot y.2 x := by
  change vecDot y.1 0 + vecDot y.2 x = _
  rw [vecDot_zero_right, zero_add]

private theorem blockVecDot_inl_quad (H : BlockMat d) (x : Vec d) :
    blockVecDot ((x, 0) : BlockVec d)
        (blockMatVecMul H ((x, 0) : BlockVec d)) =
      vecDot x (matVecMul H.upperLeft x) := by
  change vecDot x (matVecMul H.upperLeft x + matVecMul H.upperRight 0) +
      vecDot 0 (matVecMul H.lowerLeft x + matVecMul H.lowerRight 0) = _
  rw [matVecMul_zero, matVecMul_zero, add_zero, add_zero,
    vecDot_zero_left, add_zero]

private theorem blockVecDot_inr_quad (H : BlockMat d) (x : Vec d) :
    blockVecDot ((0, x) : BlockVec d)
        (blockMatVecMul H ((0, x) : BlockVec d)) =
      vecDot x (matVecMul H.lowerRight x) := by
  change vecDot 0 (matVecMul H.upperLeft 0 + matVecMul H.upperRight x) +
      vecDot x (matVecMul H.lowerLeft 0 + matVecMul H.lowerRight x) = _
  rw [matVecMul_zero, matVecMul_zero, zero_add, zero_add,
    vecDot_zero_left, zero_add]

/-- **Pairing against an inverse block form.**  For a symmetric positive
semidefinite block form with a right inverse, the plain pairing is bounded by
the form's quadratic mean of the first vector and the inverse form's quadratic
mean of the second. -/
theorem abs_blockVecDot_le_sqrt_mul_sqrt_of_inverse
    {S Sinv : BlockMat d} (hS : IsSymmetricBlockMat S)
    (hSpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul S Z))
    (hleft : blockMatMul S Sinv = blockIdentity d)
    (y Qh : BlockVec d) :
    |blockVecDot y Qh| ≤
      Real.sqrt (blockVecDot y (blockMatVecMul S y)) *
        Real.sqrt (blockVecDot Qh (blockMatVecMul Sinv Qh)) := by
  have hSz : blockMatVecMul S (blockMatVecMul Sinv Qh) = Qh := by
    rw [← blockMatVecMul_blockMatMul, hleft, blockMatVecMul_blockIdentity]
  have hcs :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hS hSpsd y
      (blockMatVecMul Sinv Qh)
  rw [hSz] at hcs
  rwa [blockVecDot_comm (blockMatVecMul Sinv Qh) Qh] at hcs

/-! ## The two diagonal Schur loads as quadratic forms -/

private theorem vecNorm_matSqrt_sq {M : Mat d} (hM : M.PosSemidef) (x : Vec d) :
    Book.Ch02.vecNorm (matVecMul (matSqrt M) x) ^ 2 =
      vecDot x (matVecMul M x) := by
  rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
  change vecDot (matVecMul (matSqrt M) x) (matVecMul (matSqrt M) x) = _
  calc vecDot (matVecMul (matSqrt M) x) (matVecMul (matSqrt M) x)
      = vecDot x (matVecMul (matTranspose (matSqrt M))
          (matVecMul (matSqrt M) x)) :=
        (vecDot_matVecMul_transpose x (matVecMul (matSqrt M) x) (matSqrt M)).symm
    _ = vecDot x (matVecMul M x) := by
        have hs : matTranspose (matSqrt M) = matSqrt M := by
          change Matrix.transpose (matSqrt M) = matSqrt M
          exact (isSymm_matSqrt M).eq
        rw [hs, matVecMul_mul, (matSqrt_spec hM).2]

/-- The flux half of the Schur load is the lower-right quadratic form. -/
theorem sq_profileSchurLoadFlux_eq {H : BlockMat d}
    (hpsd : H.lowerRight.PosSemidef) (hdet : IsUnit H.lowerRight.det)
    (Qcen : Vec d) :
    profileSchurLoadFlux H Qcen ^ 2 =
      vecDot Qcen (matVecMul H.lowerRight Qcen) := by
  have hstar : (schurSigmaStar H)⁻¹ = H.lowerRight := schurSigmaStar_inv H hdet
  rw [profileSchurLoadFlux]
  rw [vecNorm_matSqrt_sq (M := (schurSigmaStar H)⁻¹) (by rw [hstar]; exact hpsd) Qcen,
    hstar]

/-- The gradient half of the Schur load is the upper-left quadratic form. -/
theorem sq_profileSchurLoadGradient_eq {H : BlockMat d}
    (hpsd : H.upperLeft.PosSemidef) (Pcen : Vec d) :
    profileSchurLoadGradient H Pcen ^ 2 =
      vecDot Pcen (matVecMul H.upperLeft Pcen) := by
  rw [profileSchurLoadGradient, vecNorm_matSqrt_sq hpsd Pcen]

/-! ## The per-cell pairing through the starred bridge -/

/-- **The gradient-slot cell pairing.**  The potential average of a doubled
response field pairs with a load through the cell energy and the flux half of
the Schur load of the cell's response block. -/
theorem abs_vecDot_averageVec_potential_le {U : Domain d} {lam Lam : ℝ}
    (c : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) c.toCoeffField)
    (hpsd : (Book.Ch02.coarseBlockMatrix U c).lowerRight.PosSemidef)
    (hdet : IsUnit (Book.Ch02.coarseBlockMatrix U c).lowerRight.det)
    {Y : DoubledField d} (hY : IsDoubledResponseField U c Y) (Qcen : Vec d) :
    |vecDot Qcen (Book.Ch02.averageVec U Y.potential)| ≤
      Real.sqrt (Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField c x) (Y.eval x)))) *
        profileSchurLoadFlux (Book.Ch02.coarseBlockMatrix U c) Qcen := by
  classical
  set S : BlockMat d := Book.Ch02.coarseStarredBlockMatrix U c with hSdef
  set Sinv : BlockMat d := Book.Ch02.coarseStarredBlockMatrixInv U c with hSinvdef
  set y : BlockVec d :=
    ((Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) :
      BlockVec d) with hy
  have hSpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul S Z) := by
    intro Z
    by_cases hZ : Z = 0
    · subst hZ
      simp [blockVecDot, vecDot_zero_left]
    · exact ((Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_matrix_posDef
        Z hZ).le
  have hleft : blockMatMul S Sinv = blockIdentity d :=
    (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_left_inverse
  have hcs := abs_blockVecDot_le_sqrt_mul_sqrt_of_inverse
    (isSymmetricBlockMat_coarseStarredBlockMatrix c) hSpsd hleft y
    ((Qcen, 0) : BlockVec d)
  have hleftpair : blockVecDot y ((Qcen, 0) : BlockVec d) =
      vecDot Qcen (Book.Ch02.averageVec U Y.potential) := by
    rw [blockVecDot_pair_inl, hy, vecDot_comm]
  have hload : blockVecDot ((Qcen, 0) : BlockVec d)
      (blockMatVecMul Sinv ((Qcen, 0) : BlockVec d)) =
      profileSchurLoadFlux (Book.Ch02.coarseBlockMatrix U c) Qcen ^ 2 := by
    rw [blockVecDot_inl_quad, hSinvdef,
      (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_inverse_formula,
      sq_profileSchurLoadFlux_eq hpsd hdet]
    rfl
  have hloadRoot :
      Real.sqrt (blockVecDot ((Qcen, 0) : BlockVec d)
        (blockMatVecMul Sinv ((Qcen, 0) : BlockVec d))) =
        profileSchurLoadFlux (Book.Ch02.coarseBlockMatrix U c) Qcen := by
    rw [hload, Real.sqrt_sq (profileSchurLoadFlux_nonneg _ _)]
  have henergy := energy_map_le c hEll hY
  have hquad : blockVecDot y (blockMatVecMul S y) ≤
      Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField c x) (Y.eval x))) := by
    rw [hy, hSdef]
    linarith only [henergy]
  rw [hleftpair, hloadRoot] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (profileSchurLoadFlux_nonneg _ _))
  exact Real.sqrt_le_sqrt hquad

/-- **The flux-slot cell pairing.**  The flux average of a doubled response
field pairs with a load through the cell energy and the gradient half of the
Schur load of the cell's response block. -/
theorem abs_vecDot_averageVec_flux_le {U : Domain d} {lam Lam : ℝ}
    (c : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) c.toCoeffField)
    (hpsd : (Book.Ch02.coarseBlockMatrix U c).upperLeft.PosSemidef)
    {Y : DoubledField d} (hY : IsDoubledResponseField U c Y) (Pcen : Vec d) :
    |vecDot Pcen (Book.Ch02.averageVec U Y.flux)| ≤
      Real.sqrt (Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField c x) (Y.eval x)))) *
        profileSchurLoadGradient (Book.Ch02.coarseBlockMatrix U c) Pcen := by
  classical
  set S : BlockMat d := Book.Ch02.coarseStarredBlockMatrix U c with hSdef
  set Sinv : BlockMat d := Book.Ch02.coarseStarredBlockMatrixInv U c with hSinvdef
  set y : BlockVec d :=
    ((Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) :
      BlockVec d) with hy
  have hSpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul S Z) := by
    intro Z
    by_cases hZ : Z = 0
    · subst hZ
      simp [blockVecDot, vecDot_zero_left]
    · exact ((Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_matrix_posDef
        Z hZ).le
  have hleft : blockMatMul S Sinv = blockIdentity d :=
    (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_left_inverse
  have hcs := abs_blockVecDot_le_sqrt_mul_sqrt_of_inverse
    (isSymmetricBlockMat_coarseStarredBlockMatrix c) hSpsd hleft y
    ((0, Pcen) : BlockVec d)
  have hleftpair : blockVecDot y ((0, Pcen) : BlockVec d) =
      vecDot Pcen (Book.Ch02.averageVec U Y.flux) := by
    rw [blockVecDot_pair_inr, hy, vecDot_comm]
  have hload : blockVecDot ((0, Pcen) : BlockVec d)
      (blockMatVecMul Sinv ((0, Pcen) : BlockVec d)) =
      profileSchurLoadGradient (Book.Ch02.coarseBlockMatrix U c) Pcen ^ 2 := by
    rw [blockVecDot_inr_quad, hSinvdef,
      (Internal.Ch02.BookCh02.blockCoarseMatrixTheory U c).starred_inverse_formula,
      sq_profileSchurLoadGradient_eq hpsd]
    rfl
  have hloadRoot :
      Real.sqrt (blockVecDot ((0, Pcen) : BlockVec d)
        (blockMatVecMul Sinv ((0, Pcen) : BlockVec d))) =
        profileSchurLoadGradient (Book.Ch02.coarseBlockMatrix U c) Pcen := by
    rw [hload, Real.sqrt_sq (profileSchurLoadGradient_nonneg _ _)]
  have henergy := energy_map_le c hEll hY
  have hquad : blockVecDot y (blockMatVecMul S y) ≤
      Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField c x) (Y.eval x))) := by
    rw [hy, hSdef]
    linarith only [henergy]
  rw [hleftpair, hloadRoot] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (profileSchurLoadGradient_nonneg _ _))
  exact Real.sqrt_le_sqrt hquad

/-! ## The annealed Schur loads -/

/-- The flux half of the Schur load of a hatted block is the block's own
lower-right quadratic form: the hatting shear only shifts the flux slot by a
multiple of the potential slot, which vanishes here. -/
theorem sq_profileSchurLoadFlux_hatted_eq_blockQuadratic (h : Mat d)
    (H : BlockMat d)
    (hpsd : (profileHattedBlock h H).lowerRight.PosSemidef)
    (hdet : IsUnit (profileHattedBlock h H).lowerRight.det) (Qcen : Vec d) :
    profileSchurLoadFlux (profileHattedBlock h H) Qcen ^ 2 =
      blockVecDot ((0, Qcen) : BlockVec d)
        (blockMatVecMul H ((0, Qcen) : BlockVec d)) := by
  rw [sq_profileSchurLoadFlux_eq hpsd hdet, ← blockVecDot_inr_quad,
    profileHattedBlock, blockQuadratic_skewBlockCongr, matVecMul_zero, zero_add]

/-- The gradient half of the Schur load of a hatted block is the block's
quadratic form at the sheared potential load. -/
theorem sq_profileSchurLoadGradient_hatted_eq_blockQuadratic (h : Mat d)
    (H : BlockMat d)
    (hpsd : (profileHattedBlock h H).upperLeft.PosSemidef) (Pcen : Vec d) :
    profileSchurLoadGradient (profileHattedBlock h H) Pcen ^ 2 =
      blockVecDot ((Pcen, matVecMul h Pcen) : BlockVec d)
        (blockMatVecMul H ((Pcen, matVecMul h Pcen) : BlockVec d)) := by
  rw [sq_profileSchurLoadGradient_eq hpsd, ← blockVecDot_inl_quad,
    profileHattedBlock, blockQuadratic_skewBlockCongr]
  simp

/-- **The annealed flux load is the expectation of the pathwise flux load.**
The lower-right quadratic form is linear in the block, so the annealed Schur
coordinate is the coordinate of the full annealed matrix. -/
theorem integral_sq_profileSchurLoadFlux_hatted_eq
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (h : Mat d) (Qcen : Vec d)
    (hpsdA : (profileHattedBlock h (annealedBlock P U)).lowerRight.PosSemidef)
    (hdetA : IsUnit (profileHattedBlock h (annealedBlock P U)).lowerRight.det)
    (hpsd : ∀ a : CoeffSpace d,
      (profileHattedBlock h (coarseBlock U a)).lowerRight.PosSemidef)
    (hdet : ∀ a : CoeffSpace d,
      IsUnit (profileHattedBlock h (coarseBlock U a)).lowerRight.det) :
    profileSchurLoadFlux (profileHattedBlock h (annealedBlock P U)) Qcen ^ 2 =
      ∫ a, profileSchurLoadFlux (profileHattedBlock h (coarseBlock U a))
        Qcen ^ 2 ∂P := by
  rw [sq_profileSchurLoadFlux_hatted_eq_blockQuadratic h (annealedBlock P U)
    hpsdA hdetA Qcen, blockVecDot_blockMatVecMul_annealedBlock hint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
  exact (sq_profileSchurLoadFlux_hatted_eq_blockQuadratic h (coarseBlock U a)
    (hpsd a) (hdet a) Qcen).symm

/-- **The annealed gradient load is the expectation of the pathwise gradient
load.** -/
theorem integral_sq_profileSchurLoadGradient_hatted_eq
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (h : Mat d) (Pcen : Vec d)
    (hpsdA : (profileHattedBlock h (annealedBlock P U)).upperLeft.PosSemidef)
    (hpsd : ∀ a : CoeffSpace d,
      (profileHattedBlock h (coarseBlock U a)).upperLeft.PosSemidef) :
    profileSchurLoadGradient (profileHattedBlock h (annealedBlock P U)) Pcen ^ 2 =
      ∫ a, profileSchurLoadGradient (profileHattedBlock h (coarseBlock U a))
        Pcen ^ 2 ∂P := by
  rw [sq_profileSchurLoadGradient_hatted_eq_blockQuadratic h (annealedBlock P U)
    hpsdA Pcen, blockVecDot_blockMatVecMul_annealedBlock hint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
  exact (sq_profileSchurLoadGradient_hatted_eq_blockQuadratic h
    (coarseBlock U a) (hpsd a) Pcen).symm

/-! ## The scale-sum premise of the row closers -/

end

end HCPolySupport.HighContrast.Response
