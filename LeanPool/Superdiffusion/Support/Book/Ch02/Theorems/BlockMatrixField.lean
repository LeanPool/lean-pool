/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.BlockMatrixField

/-!
# BlockMatrixField

Ported from scottnarmstrong/CoarseGraining at c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace HCPolySupport
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 block-matrix field algebra theorem
`l.block.matrix.field.basic.definitions`. -/
theorem blockMatrixFieldAlgebraTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    BlockMatrixFieldAlgebraTheory U a :=
  HCPolySupport.Internal.Ch02.BookCh02.blockMatrixFieldAlgebraTheory U a

end

end Ch02
end Book
end HCPolySupport
