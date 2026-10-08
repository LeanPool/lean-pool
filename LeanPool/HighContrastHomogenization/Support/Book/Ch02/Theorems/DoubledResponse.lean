/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledResponse

/-!
# Coarse-graining support: Support.Book.Ch02.Theorems.DoubledResponse

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch02

noncomputable section

/-- Public Chapter 2 doubled-response theorem package for
`l.block.response.functional.basic.definitions`.

The coefficient field is used through the a.e. public `CoeffOn` interface; no
pointwise ellipticity or representative choice is exposed. -/
theorem doubledResponseTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    DoubledResponseTheory U a :=
  HCPolySupport.Internal.Ch02.BookCh02.doubledResponseTheory U a

end

end Ch02
end Book
end HCPolySupport
