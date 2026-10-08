/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Setup.Moments
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace

/-!
# High-contrast homogenization: Entry.Setup.NormalizedFluctuation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed adapted block, the normalized mean `P^q_{j,k}` and the fluctuation `V^q_{j,k}`

Near `e.scale.selection.normalized.mean.fluctuation`:

> For `j ∈ ℤ`, set `⋄_j^q := q □_j` and `𝐀hom_{j,q} := 𝐀hom(⋄_j^q) = E[𝐀(⋄_j^q)]`.  For
> `j ≤ k` and `z ∈ 3^j q ℤ^d`, define the normalized mean and fluctuation by
> `P^q_{j,k} := 𝐀hom_{k,q}^{-1/2} 𝐀hom_{j,q} 𝐀hom_{k,q}^{-1/2}` and
> `V^q_{j,k}(z) := 𝐀hom_{k,q}^{-1/2}(𝐀(z + ⋄_j^q) − 𝐀hom_{j,q})𝐀hom_{k,q}^{-1/2}`.
> … Write `V^q_j := V^q_{j,j}(0)`.

`𝐀(U)` is `coarseBlock U`, `𝐀hom(U)` is `annealedBlock P U` and `⋄_j^q` is `adaptedCell q j`;
the conjugation `F^{-1/2} · F^{-1/2}` is `normalizedBlock` of
`HCPoly/Entry/Setup/ProjectiveDistance.lean`.

Two things the print carries as hypotheses and these definitions do not, so that a reader
comparing file to manuscript finds no silent divergence (operating rules, the standing
honesty rule):

* `j ≤ k`.  `relMean` and `normalizedFluctuation` are total in both generations.
* `z ∈ 3^j q ℤ^d`.  `normalizedFluctuation` takes an arbitrary translate `z : Vec d`
  through `adaptedCellTranslate`; the aligned centers are `adaptedLatticeAtScale q j` of
  `HCPoly/Entry/Setup/AdaptedGridCells.lean`, and a consumer that needs the printed restriction
  states it.
  The one printed use of a non-aligned argument is `V^q_j = V^q_{j,j}(0)`, and `0` is
  aligned.

`𝐀hom_{k,q}^{-1/2}` is meaningful because the annealed adapted block is positive definite;
that is `blockPosDef_annealedBlock` (`HCPoly/Setup/Response.lean`), which has
hypotheses.  None of them is imposed here: off the positive definite blocks the inverse and
the square root take the junk values fixed in `HCPoly/Setup/BlockAlgebra.lean`.

The print names the random matrix `V^q_{j,k}(z)` and takes norms of it at the use sites;
`normalizedFluctuation` defines that matrix itself, not its mixed norm.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockSub coarseBlock normalizedBlock)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-- The normalized fluctuation
`V^q_{j,k}(z) = 𝐀hom_{k,q}^{-1/2}(𝐀(z + ⋄_j^q) − 𝐀hom_{j,q})𝐀hom_{k,q}^{-1/2}`
(`e.scale.selection.normalized.mean.fluctuation`), a random doubled block. -/
@[expose]
def normalizedFluctuation (P : Measure (CoeffSpace d)) (q : Mat d) (j k : ℤ) (z : Vec d)
    (a : CoeffSpace d) : BlockMat d :=
  normalizedBlock
    (blockSub (coarseBlock (adaptedCellTranslate q j z) a) (adaptedMean P q j))
    (adaptedMean P q k)

/-- The diagonal fluctuation `V^q_j = V^q_{j,j}(0)` (near `e.scale.selection.logdet.loss`). -/
@[expose]
def normalizedFluctuationSelf (P : Measure (CoeffSpace d)) (q : Mat d) (j : ℤ)
    (a : CoeffSpace d) : BlockMat d :=
  normalizedFluctuation P q j j 0 a

end

end HCPolySupport.HighContrast
