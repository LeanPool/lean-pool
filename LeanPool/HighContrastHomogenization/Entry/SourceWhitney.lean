/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic

/-!
# High-contrast homogenization: Entry.SourceWhitney

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `l.source.whitney`

This file attaches the rounded-grid geometry theorem to the
`HCPoly/Entry/Statements/SourceWhitney.lean` interface.  It does not import or consume that
statement.
-/

namespace HCPolySupport.HighContrast.Entry

open MeasureTheory

/-- Proof of `l.source.whitney`.

The statement carries the standing paper assumption `hd : 2 <= d`;
the geometry theorem needs only the resulting local `NeZero d` instance. -/
theorem source_whitney
    (d : ℕ) (hd : 2 ≤ d)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : Matrix.PosDef m)
    (j : ℤ) (y : Vec d) :
    (∀ p ∈ Geometry.maximalCellPairs
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) j,
        HighContrast.standardCell d p.1 p.2 ⊆
          HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) ∧
      (Geometry.maximalCellPairs
        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
          j).PairwiseDisjoint
        (fun p => HighContrast.standardCell d p.1 p.2) ∧
      volume (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y \
        ⋃ p ∈ Geometry.maximalCellPairs
          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) j,
          HighContrast.standardCell d p.1 p.2) = 0 ∧
      ∀ r ≤ j,
        ∃ hfin : (Geometry.maximalCellIndices
          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y) j
            r).Finite,
          ∑ w ∈ hfin.toFinset,
              (volume (HighContrast.standardCell d r w)).toReal /
                (volume (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar
                  m) j y)).toReal ≤
            12 * (d : ℝ) ^ ((3 : ℝ) / 2) * (3 : ℝ) ^ (r - j) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
  exact Geometry.source_whitney_roundedGrid hj hm j y

end HCPolySupport.HighContrast.Entry
