/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq

/-!
# Coarse-graining support: Support.Book.Ch02.Theorems.HomogenizationError.Public

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace HCPolySupport
namespace Book
namespace Ch02

noncomputable section


/-!
# Public Chapter 2.5 HCPolySupport Error Package

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

/-- Aggregate unconditional public theorem package for the Sec. 2.5
homogenization-error facts currently needed downstream. -/
theorem homogenizationErrorTheory (d : ℕ) [NeZero d] :
    HomogenizationErrorTheory d := by
  refine ⟨?_⟩
  intro Q a a0
  exact homogenizationErrorInfinityOneBasicTheory Q a a0

end

end Ch02
end Book
end HCPolySupport
