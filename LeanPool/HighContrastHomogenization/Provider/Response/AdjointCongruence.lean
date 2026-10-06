/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.VariationalIdentities

/-!
# High-contrast homogenization: Provider.Response.AdjointCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coefficient-transpose congruence of the coarse block

The adjoint half of the weak-norm estimate for the optimizer state and the
adjoint line of the corrected centered response both rest on a single
algebraic identity: for the transposed coefficient field the coarse Schur data
are `(σ, σ_*, -κ)`, so

  `𝐀(V;aᵗ) = D𝐀(V;a)D`,  `D = diag(I, -I)`

in the form the response estimate of `p.response.transfer` uses.  Both printed
sign conventions for `D` — `diag(-I, I)` and `diag(I, -I)` — give the same
congruence, since the two differ by an overall sign.

`BlockCoarseMatrixTheory` supplies `σ(V;aᵗ) = σ(V;a)`, `σ_*(V;aᵗ) = σ_*(V;a)`
and `κ(V;aᵗ) = -κ(V;a)`.  The Schur block formula [Armstrong–Kuusi, (2.13)] is written
over `σ_*^{-1}` rather than over `σ_*`, so the middle clause has to be upgraded
to the inverse; that is done here from the magic identities, which show that the
pure flux response `J(V,0,q;·)` is insensitive to transposition.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- **The pure flux response is insensitive to transposition**: `J(V,0,q;aᵗ) =
J(V,0,q;a)`.  Both sides equal `½q·σ_*^{-1}(V;a)q`, the first by the adjoint
quadratic identity and the second by the completed square. -/
theorem responseJ_transpose_zero_left {U : Domain d} (a : CoeffOn U) (q : Vec d) :
    Book.Ch02.responseJ U a.transpose 0 q = Book.Ch02.responseJ U a 0 q := by
  have hM := Internal.Ch02.BookCh02.responseMagicIdentitiesTheory U a
  rw [hM.adjoint_quadratic 0 q, hM.completed_square 0 q]
  simp [matVecMul_zero, vecDot_zero_left]

/-- **The inverse Schur block is insensitive to transposition**:
`σ_*^{-1}(V;aᵗ) = σ_*^{-1}(V;a)`.  The canonical extraction reads
`σ_*^{-1}` off the pure flux response alone. -/
theorem sigmaStarInvCoarse_transpose {U : Domain d} (a : CoeffOn U) :
    Book.Ch02.sigmaStarInvCoarse U a.transpose = Book.Ch02.sigmaStarInvCoarse U a := by
  ext i j
  show Book.Ch02.sigmaStarInvEntry U a.transpose i j = Book.Ch02.sigmaStarInvEntry U a i j
  unfold Book.Ch02.sigmaStarInvEntry
  by_cases h : i = j <;>
    simp [h, responseJ_transpose_zero_left]

/-- **The derived block `b = σ + κᵗσ_*^{-1}κ` is insensitive to transposition**,
the sign of `κ` cancelling in the quadratic correction. -/
theorem bCoarse_transpose {U : Domain d} (a : CoeffOn U) :
    Book.Ch02.bCoarse U a.transpose = Book.Ch02.bCoarse U a := by
  have hT := Internal.Ch02.BookCh02.blockCoarseMatrixTheory U a
  show Book.Ch02.sigmaCoarse U a.transpose +
      matTranspose (Book.Ch02.kappaCoarse U a.transpose) *
          Book.Ch02.sigmaStarInvCoarse U a.transpose *
        Book.Ch02.kappaCoarse U a.transpose =
    Book.Ch02.sigmaCoarse U a +
      matTranspose (Book.Ch02.kappaCoarse U a) * Book.Ch02.sigmaStarInvCoarse U a *
        Book.Ch02.kappaCoarse U a
  rw [hT.adjoint_sigma, hT.adjoint_kappa, sigmaStarInvCoarse_transpose,
    show matTranspose (-Book.Ch02.kappaCoarse U a) = -matTranspose (Book.Ch02.kappaCoarse U a) from
      Matrix.transpose_neg _]
  simp

/-- The `D`-congruence of a doubled block matrix flips the sign of the two
off-diagonal corners. -/
theorem blockMatMul_blockDiag_one_neg_one (A : BlockMat d) :
    blockMatMul (blockDiag 1 (-1)) (blockMatMul A (blockDiag (1 : Mat d) (-1))) =
      { upperLeft := A.upperLeft
        upperRight := -A.upperRight
        lowerLeft := -A.lowerLeft
        lowerRight := A.lowerRight } := by
  simp [blockMatMul, blockDiag]

/-- **The coefficient-transpose congruence**, the adjoint congruence of the
coarse block used by the response estimate of `p.response.transfer`:
`𝐀(V;aᵗ) = D𝐀(V;a)D` with `D = diag(I, -I)`. -/
theorem coarseBlockMatrix_transpose {U : Domain d} (a : CoeffOn U) :
    Book.Ch02.coarseBlockMatrix U a.transpose =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (Book.Ch02.coarseBlockMatrix U a) (blockDiag 1 (-1))) := by
  have hT := Internal.Ch02.BookCh02.blockCoarseMatrixTheory U a
  rw [blockMatMul_blockDiag_one_neg_one]
  have hUL : Book.Ch02.bCoarse U a.transpose = Book.Ch02.bCoarse U a := bCoarse_transpose a
  have hUR : -(matTranspose (Book.Ch02.kappaCoarse U a.transpose) *
        Book.Ch02.sigmaStarInvCoarse U a.transpose) =
      -(-(matTranspose (Book.Ch02.kappaCoarse U a) * Book.Ch02.sigmaStarInvCoarse U a)) := by
    rw [hT.adjoint_kappa, sigmaStarInvCoarse_transpose,
      show matTranspose (-Book.Ch02.kappaCoarse U a) =
        -matTranspose (Book.Ch02.kappaCoarse U a) from Matrix.transpose_neg _]
    simp
  have hLL : -(Book.Ch02.sigmaStarInvCoarse U a.transpose *
        Book.Ch02.kappaCoarse U a.transpose) =
      -(-(Book.Ch02.sigmaStarInvCoarse U a * Book.Ch02.kappaCoarse U a)) := by
    rw [hT.adjoint_kappa, sigmaStarInvCoarse_transpose]
    simp
  have hLR : Book.Ch02.sigmaStarInvCoarse U a.transpose = Book.Ch02.sigmaStarInvCoarse U a :=
    sigmaStarInvCoarse_transpose a
  show ({ upperLeft := Book.Ch02.bCoarse U a.transpose
          upperRight := -(matTranspose (Book.Ch02.kappaCoarse U a.transpose) *
            Book.Ch02.sigmaStarInvCoarse U a.transpose)
          lowerLeft := -(Book.Ch02.sigmaStarInvCoarse U a.transpose *
            Book.Ch02.kappaCoarse U a.transpose)
          lowerRight := Book.Ch02.sigmaStarInvCoarse U a.transpose } : BlockMat d) = _
  rw [hUL, hUR, hLL, hLR]
  simp

end

end Response
end HighContrast
end HCPolySupport
