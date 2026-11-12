/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: NoCheckerboardCellVertex]

/-!
# NoCheckerboardCellVertex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A cell set has *no checkerboard lattice vertex* when, among the four
unit cells incident with any lattice vertex, the occupied cells are never
exactly one diagonally opposite pair.  In lower-left-corner coordinates the
four incident cells at $z$ are
$z,z-1,z-i,z-1-i$; the forbidden patterns are
$\{z,z-1-i\}$ and $\{z-1,z-i\}$.
-/
def NoCheckerboardCellVertex (S : Set LatticeCell) : Prop :=
-- BODY
  ∀ z : GaussianInt,
    ¬ ((z ∈ S ∧ z - 1 - ⟨0, 1⟩ ∈ S ∧
          z - 1 ∉ S ∧ z - ⟨0, 1⟩ ∉ S) ∨
       (z - 1 ∈ S ∧ z - ⟨0, 1⟩ ∈ S ∧
          z ∉ S ∧ z - 1 - ⟨0, 1⟩ ∉ S))

end ApollonianSuperharmonic

end
