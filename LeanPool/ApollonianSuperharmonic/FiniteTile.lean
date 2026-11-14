/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: FiniteTile]

/-!
# FiniteTile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A finite lattice-cell family is a finite set of lattice cells.  We represent
it by the finite set of their lower-left corners in $\mathbb Z[i]$.  At this
stage no connectedness or disk condition is imposed.
-/
abbrev FiniteTile : Type :=
-- BODY
  Finset LatticeCell

end ApollonianSuperharmonic

end
