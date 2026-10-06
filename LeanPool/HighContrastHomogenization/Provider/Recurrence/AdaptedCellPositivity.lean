/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedCellPositivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise symmetry and positivity of the response over adapted cells

The first of the coarse-block properties taken from HC asserts that the coarse
block response `𝐀(U; a)` of a Lipschitz cell is, pathwise in the coefficient
field, a symmetric positive definite doubled matrix.  For the adapted cubes
`⋄_j^q = q□_j` of a rounded geometry and their aligned translates
`3^j q w + ⋄_j^q` this file proves both halves.

Symmetry needs no hypothesis at all: the coarse block response of *any* subset
of `ℝ^d` is symmetric, the off-diagonal entries being the polarization of the
variational quantity.

Positivity is the deterministic coarse-graining theory of a bounded open convex
domain, transported to the adapted cell.  A rounded adapted grid is invertible,
so the adapted cell is a nonempty bounded open convex domain, hence a chapter 2
domain; the coarse response of a field of the coefficient space on it is then the
chapter 2 coarse block matrix of that field read as a coefficient object, which
is positive definite.

Two consequences are recorded for the fixed-grid recurrence.  The annealed block
of an adapted cell inherits positivity as soon as the response is integrable, so
the positivity binders on the adapted means `E_j^q` follow from the finiteness
binders.  And the Schur ordering `σ_* ≤ σ` becomes available on every adapted
cell, as it already was on every centered cube.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The pathwise symmetry clause -/

/-- **The coarse response on an adapted cell is symmetric**, pathwise in the
coefficient field.  This is the symmetry half of the first of the coarse-block
properties taken from HC; it holds on every subset of `ℝ^d`. -/
theorem isSymmetricBlockMat_coarseBlock_adaptedCell (q : Mat d) (j : ℤ)
    (a : CoeffSpace d) : IsSymmetricBlockMat (coarseBlock (adaptedCell q j) a) :=
  isSymmetricBlockMat_coarseBlockMatrix (adaptedCell q j) ⇑a.1

/-- **The coarse response on an aligned adapted cell is symmetric**, pathwise in
the coefficient field. -/
theorem isSymmetricBlockMat_coarseBlock_adaptedCellAt (q : Mat d) (r : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    IsSymmetricBlockMat (coarseBlock (adaptedCellAt q r w) a) :=
  isSymmetricBlockMat_coarseBlockMatrix (adaptedCellAt q r w) ⇑a.1

/-- **The adapted response `A_r^q(z)` is symmetric**, in the carrier the
fixed-grid estimates are written in. -/
theorem isSymmetricBlockMat_adaptedResponse (q : Mat d) (r : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) : IsSymmetricBlockMat (adaptedResponse q r w a) :=
  isSymmetricBlockMat_coarseBlock_adaptedCellAt q r w a

/-! ## The pathwise positivity clause -/

/-- The coarse response of a field of the coefficient space is positive definite
on every bounded open convex nonempty domain: it is the chapter 2 coarse block
matrix of the field read as a coefficient object on that domain. -/
theorem blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock U a) := by
  exact HCPolySupport.HighContrast.blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
    hU hne a

/-- **The coarse response on an adapted cell is positive definite**, pathwise in
the coefficient field.  This is the positivity half of the first of the
coarse-block properties taken from HC, at the cells the fixed-grid recurrence is
written on. -/
theorem blockPosDef_coarseBlock_adaptedCell {q : Mat d} (hq : q.PosDef) (j : ℤ)
    (a : CoeffSpace d) : Book.Ch02.BlockPosDef (coarseBlock (adaptedCell q j) a) :=
  blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCell hq j) (adaptedCell_nonempty q j) a

/-- **The coarse response on an aligned adapted cell is positive definite**,
pathwise in the coefficient field. -/
theorem blockPosDef_coarseBlock_adaptedCellAt {q : Mat d} (hq : q.PosDef) (r : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock (adaptedCellAt q r w) a) :=
  blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellAt hq r w) (adaptedCellAt_nonempty q r w) a

/-- **The adapted response is positive definite**, in the carrier the fixed-grid
estimates are written in. -/
theorem blockPosDef_adaptedResponse {q : Mat d} (hq : q.PosDef) (r : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (adaptedResponse q r w a) :=
  blockPosDef_coarseBlock_adaptedCellAt hq r w a

/-- The pathwise positivity clause at a rounded adapted grid: no positivity
hypothesis on the grid is needed, since a rounded grid is positive definite. -/
theorem blockPosDef_coarseBlock_adaptedCell_of_isRoundedGrid {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) (j : ℤ) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock (adaptedCell q j) a) :=
  blockPosDef_coarseBlock_adaptedCell (posDef_of_isRoundedGrid hq) j a

/-! ## The annealed block of an adapted cell -/

/-- **The adapted mean `E_r^q` is positive definite** as soon as it is an
expectation at all.  The pathwise positivity of the response integrates, so the
positivity binders of `p.fixed.geometry.parent.child.recurrence` follow from its finiteness
binders on a rounded adapted grid. -/
theorem blockPosDef_adaptedMean {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (r : ℤ) (hint : HasFiniteAdaptedMean P q r) :
    Book.Ch02.BlockPosDef (adaptedMean P q r) :=
  blockPosDef_annealedBlock hint (blockPosDef_coarseBlock_adaptedCell hq r)

/-- The adapted mean of a rounded adapted grid is positive definite as soon as
it is finite: the grid's own positivity is part of `IsRoundedGrid`. -/
theorem blockPosDef_adaptedMean_of_isRoundedGrid {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) (r : ℤ)
    (hint : HasFiniteAdaptedMean P q r) : Book.Ch02.BlockPosDef (adaptedMean P q r) :=
  blockPosDef_adaptedMean (posDef_of_isRoundedGrid hq) r hint

/-- **The annealed block of an aligned adapted cell is positive definite** as
soon as the coarse response is integrable over the law. -/
theorem blockPosDef_annealedBlock_adaptedCellAt {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {q : Mat d} (hq : q.PosDef) (r : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q r w)) :
    Book.Ch02.BlockPosDef (annealedBlock P (adaptedCellAt q r w)) :=
  blockPosDef_annealedBlock hint (blockPosDef_coarseBlock_adaptedCellAt hq r w)

/-! ## The Schur ordering on an adapted cell -/

end

end Recurrence
end HighContrast
end HCPolySupport
