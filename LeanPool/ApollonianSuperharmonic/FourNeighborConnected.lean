/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: FourNeighborConnected]

/-!
# FourNeighborConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A set of lattice cells is *four-neighbor connected* when it is
nonempty and every two of its cells can be joined by a finite list of cells
in the set, each consecutive pair sharing a complete unit side in the sense
of `FourNeighborAdjacent`.
-/
def FourNeighborConnected (S : Set LatticeCell) : Prop :=
-- BODY
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ p : List LatticeCell,
    p.head? = some x ∧ p.getLast? = some y ∧
    (∀ z ∈ p, z ∈ S) ∧
    ∀ a b : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
      p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b

end ApollonianSuperharmonic

end
