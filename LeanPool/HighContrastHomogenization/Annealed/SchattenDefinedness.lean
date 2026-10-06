/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SourceObjects
public import LeanPool.HighContrastHomogenization.Annealed.Contrast
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Annealed.SchattenDefinedness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Definedness obligations for the Schatten encoding

The Schatten norm is written with the continuous functional calculus of the
square of a symmetric doubled block matrix.  The calculus is a total function:
off its predicate it returns zero, and the Schatten norm would then be zero
rather than large.  This file discharges the obligations that show the predicate
is met at every argument the fixed-grid statements evaluate it on, so that the
encoding never returns that value.

The chain is: a symmetric doubled block matrix is self-adjoint as a `2d × 2d`
real matrix; the positive semidefinite square root is symmetric, and remains so
on its own junk branch, where it is the identity; conjugation by a symmetric
matrix preserves symmetry, so the normalized block of a symmetric block by an
arbitrary block is symmetric; and the square of a self-adjoint matrix is
self-adjoint.  The coarse response and the annealed block are symmetric with no
hypothesis, so the conclusion is unconditional at every argument the fixed-grid
statements form.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Symmetry and self-adjointness of a doubled block matrix -/

/-- **Obligation O1.**  A symmetric doubled block matrix is self-adjoint as a
`2d × 2d` real matrix; this is the predicate of the continuous functional
calculus that the Schatten norm evaluates. -/
theorem isSelfAdjoint_toFullBlockMat {A : BlockMat d} (hA : IsSymmetricBlockMat A) :
    IsSelfAdjoint (toFullBlockMat A) :=
  isHermitian_of_isSymm (isSymm_toFullBlockMat hA)

/-- The square of a self-adjoint element is self-adjoint. -/
theorem isSelfAdjoint_mul_self {R : Type*} [Ring R] [StarRing R] {x : R}
    (hx : IsSelfAdjoint x) : IsSelfAdjoint (x * x) := by
  rw [IsSelfAdjoint, star_mul, hx.star_eq]

/-! ## Obligation O2 — the square root and the normalization -/

/-- **Obligation O2, first half.**  The positive semidefinite square root is
symmetric — on positive semidefinite data because the root is, and off it
because the junk value is the identity. -/
theorem isSymm_matSqrt {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : (matSqrt M).IsSymm := by
  rw [matSqrt]
  split
  · rename_i h
    exact isSymm_of_isHermitian h.choose_spec.1.1
  · exact Matrix.isSymm_one

/-- Conjugation by a symmetric matrix preserves symmetry. -/
theorem isSymm_mul_mul {n : Type*} [Fintype n] {S H : Matrix n n ℝ}
    (hS : S.IsSymm) (hH : H.IsSymm) : (S * H * S).IsSymm := by
  show (S * H * S).transpose = S * H * S
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hS.eq, hH.eq, ← Matrix.mul_assoc]

/-- **Obligation O2, second half.**  The normalized block of a symmetric block is
symmetric, whatever the normalizing block. -/
theorem isSymmetricBlockMat_normalizedBlock {H F : BlockMat d}
    (hH : IsSymmetricBlockMat H) :
    IsSymmetricBlockMat (normalizedBlock H F) :=
  isSymmetricBlockMat_of_isSymm
    (isSymm_mul_mul (isSymm_matSqrt _) (isSymm_toFullBlockMat hH))

/-! ## The Schatten argument is never the junk branch -/

/-- The difference of two symmetric doubled block matrices is symmetric. -/
theorem isSymmetricBlockMat_blockSub {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B) :
    IsSymmetricBlockMat (blockSub A B) := by
  intro α β
  have hA' := hA α β
  have hB' := hB α β
  cases α <;> cases β <;>
    simp only [blockSub, blockMatEntry, Matrix.sub_apply] at hA' hB' ⊢ <;>
    linarith only [hA', hB']

/-- The relative mean of the portable profile is symmetric, so the trace that
`𝔥_Q` reads is the trace of the printed `P_{j,T}^q`. -/
theorem isSymmetricBlockMat_relMean (P : Measure (CoeffSpace d)) (q : Mat d)
    (j T : ℤ) : IsSymmetricBlockMat (relMean P q j T) :=
  isSymmetricBlockMat_normalizedBlock (isSymmetricBlockMat_annealedBlock P _)

end

end HighContrast
end HCPolySupport
