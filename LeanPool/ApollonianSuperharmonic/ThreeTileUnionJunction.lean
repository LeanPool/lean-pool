/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

/-!
# Three-tile union junctions

Shared junction conditions adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Three cell-disjoint disk tiles with disk pairwise and total unions and common edges. -/
abbrev ThreeTileUnionJunction (A B C : ProtoTile) : Prop :=
  ∃ AB BC CA ABC : ProtoTile,
    LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
    LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧
    Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧
    (∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
    (∀ z : LatticeCell, z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
    (∀ z : LatticeCell, z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
    (∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
    (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
    (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
    (FootprintEdges C ∩ FootprintEdges A).Nonempty

end ApollonianSuperharmonic

end
