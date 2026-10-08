/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliDilationTransport

/-!
# Coarse-graining support: Support.Book.Ch03.Theorems.CoarseCaccioppoli

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch03

/-!
# Public coarse Caccioppoli theorem

This is the canonical public module for the homogeneous coarse Caccioppoli
theorem.  It re-exports the final apex theorem proved in
`CoarseCaccioppoliDilationTransport`, while keeping the public import path
stable for downstream note-facing consumers.
-/

noncomputable section

end

end Ch03
end Book
end HCPolySupport
