/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FiniteTile

-- [TABLET NODE: ProtoTile]

/-!
# ProtoTile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A prototile consists of a finite lattice-cell family $T$ together with a
lattice point called its anchor.  For a nonempty family the anchor is
auxiliary; for the empty, curvature-zero prototile it is its singleton
footprint and centroid.  This is the paper's degenerate convention and does
not assert that a prototile is a topological disk.
-/
structure ProtoTile where
-- BODY
  /-- The finite family of constituent unit cells, indexed by their lower-left corners. -/
  cells : FiniteTile
  /-- The auxiliary lattice vertex defining the footprint and centroid in the empty case. -/
  anchor : GaussianInt

end ApollonianSuperharmonic

end
