/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Setup.Geometry

/-!
# High-contrast homogenization: Entry.Geometry.MaximalCellsDef

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Maximal standard aligned cubes in a set — definitions only

The family of `l.source.whitney`: the standard aligned
cubes contained in a set `W` with generation at most `j`, the maximal ones among them, their
index pairs, and the centers `𝒵_r(W)` of one generation recorded by index.

This module is a definition-only leaf: it holds the four definitions the statement of
`l.source.whitney` reaches and nothing else.  The order-theoretic facts (the parent of a
maximal cube escapes `W`, distinct maximal cubes are disjoint, existence of a maximal cube
above a member) live in `HCPoly.Entry.Geometry.MaximalCells`, which imports this module.

`standardCell` itself is *not* split off: `centeredCube` and `standardCell` are in the closure of
`polynomial_entry` and remain in `HCPoly/Entry/Geometry/StandardCell.lean`.
-/

open HCPolySupport.HighContrast (standardCell)
namespace HCPolySupport.HighContrast.Geometry

variable {d : ℕ}

/-- `standardCell d k w` is a member of the family: generation at most `j` and contained in
`W`. -/
@[expose]
def IsCellIn (W : Set (Vec d)) (j k : ℤ) (w : Fin d → ℤ) : Prop :=
  k ≤ j ∧ standardCell d k w ⊆ W

/-- `standardCell d k w` is a maximal member of the family of standard aligned cubes
contained in `W` with generation at most `j`: it belongs to the family and every member
containing it is equal to it. -/
@[expose]
def IsMaximalCellIn (W : Set (Vec d)) (j k : ℤ) (w : Fin d → ℤ) : Prop :=
  IsCellIn W j k w ∧
    ∀ k' w', IsCellIn W j k' w' → standardCell d k w ⊆ standardCell d k' w' →
      standardCell d k' w' = standardCell d k w

/-- The centers `𝒵_r(W)` of the maximal cubes at generation `r`, recorded by their indices
`w` (the center is `3^r w`). -/
@[expose]
def maximalCellIndices (W : Set (Vec d)) (j r : ℤ) : Set (Fin d → ℤ) :=
  {w | IsMaximalCellIn W j r w}

/-- The index pairs `(k, w)` of all maximal cubes. -/
@[expose]
def maximalCellPairs (W : Set (Vec d)) (j : ℤ) : Set (ℤ × (Fin d → ℤ)) :=
  {p | IsMaximalCellIn W j p.1 p.2}

end HCPolySupport.HighContrast.Geometry
