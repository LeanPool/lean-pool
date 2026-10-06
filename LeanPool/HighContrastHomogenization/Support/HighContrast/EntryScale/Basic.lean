/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module


/-!
# Coarse-graining support: Support.HighContrast.EntryScale.Basic

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section
/-!
# Basic metadata for the entry-scale assembly

This file contains only source-control metadata for the development.
Mathematical theorem statements should be introduced only after their source
labels and dependency role are recorded.
-/

namespace HCPolySupport.HighContrast.EntryScale

/-- A stable label referencing a statement in the source document. -/
structure SourceLabel where
  file : String
  label : String
  line : Nat
deriving DecidableEq, Repr

namespace SourceLabel

/-- A label from the high-moment paper (Armstrong–Kuusi–Loher, to appear). -/
@[expose]
def highMomentPaper (label : String) (line : Nat) : SourceLabel :=
  { file := "high-moment-paper", label, line }
end SourceLabel
end HCPolySupport.HighContrast.EntryScale
