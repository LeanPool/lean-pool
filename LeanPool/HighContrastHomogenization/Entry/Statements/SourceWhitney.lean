/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Entry.Geometry.MaximalCellsDef
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.SourceWhitney

/-!
# High-contrast homogenization: Entry.Statements.SourceWhitney

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lemma `l.source.whitney` — standard cubes inside an adapted cube

`l.source.whitney`, the paper's Lemma "Standard cubes inside an adapted cube",
transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* `𝔪 > 0` is `Matrix.PosDef m`; `𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar m`, whose entries
depend on
  `j_*`. The notation section fixes `j_* ∈ ℕ` with `3^{j_*} ≥ 2d` (near `e.rounded.grid.bounds`);
  that standing
  constraint is the hypothesis `hj`, exactly as the definition's own theorems carry it. The ambient
  dimension is the standing `d ≥ 2` of `t.polynomial.entry`, the hypothesis `hd`.
* `W = y + ⋄_j^q` is `HighContrast.adaptedCellTranslate q j y`; the standard aligned cube `□_r` at
index
  `w` is `HighContrast.standardCell d r w`; the maximal standard aligned cubes contained in `W` with
  generation at most `j` are `Geometry.maximalCellPairs W j`, and `𝒵_r(W)` is
  `Geometry.maximalCellIndices W j r` (centers recorded by index; the center is `3^r w`).
* "partition `W` up to a null set" is the first three conjuncts: each selected cube lies in `W`,
  distinct selected cubes are disjoint, and `W` minus their union is null.
* The print sums over `𝒵_r(W)` without saying the family is finite; the fourth conjunct asserts
  finiteness of each generation's family (`∃ hfin`) and then the printed bound
  `Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}` for `r ≤ j`. Nothing is assumed beyond the
  display.

The proof in `HCPoly/Entry/SourceWhitney.lean` derives the local NeZero d instance
from hd and applies Geometry.source_whitney_roundedGrid.
-/

namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Lemma `l.source.whitney`**. Let `𝔪 > 0`, `q = 𝒬(𝔪)`, and
`W = y + ⋄_j^q` with `y ∈ ℝ^d`, `j ∈ ℤ`. The maximal standard aligned cubes contained in `W` with
generations at most `j` partition `W` up to a null set, and, with `𝒵_r(W)` their centers at
generation `r`, `Σ_{z ∈ 𝒵_r(W)} |□_r| / |W| ≤ 12 d^{3/2} 3^{r-j}` for `r ≤ j`. -/
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
  exact HCPolySupport.HighContrast.Entry.source_whitney d hd jStar hj m hm j y


end HCPolySupport.HighContrast
