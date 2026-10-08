/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Setup.Moments
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# High-contrast homogenization: Entry.Setup.AdaptedGridCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted Grid Cells

The adapted grid, the exponents the scale selection is stated with, and the cells of the adapted
grid the printed statements name.  The aligned cells and the scaled lattice are the adapted-grid
part fixed near `e.rounded.grid.bounds`; the fixed even moment and its exponent are those of
`e.scale.selection.Q.choice`; and the maximal aligned families are the centred families of the
two-grid Whitney lemma `l.two.grid.whitney`.
-/

section
/-!
## The aligned cells of an adapted grid

Near `e.rounded.grid.bounds` the paper fixes the rounded geometry `q = 𝒬(𝔪)` and the
adapted cell `⋄_j^q = q □_j`, and then indexes everything by the aligned centers
`z ∈ 3^j q ℤ^d`: the fluctuation `V^q_{j,k}(z)` is read on `z + ⋄_j^q` (near
`e.scale.selection.normalized.mean.fluctuation`), the
fluctuation history maximizes over `z ∈ 3^j q ℤ^d ∩ ⋄_m^q` (near
`e.scale.selection.fluctuation.history`), and the Whitney
families of `l.two.grid.whitney` are families of cells `z + ⋄_r^q` with `z ∈ 3^r q ℤ^d`.

`HCPoly/Setup/Geometry.lean` has `adaptedCell q j` and the translate
`adaptedCellTranslate q j y` by an arbitrary vector.  This file adds the aligned part: the
center `3^j q w` of the cell at the integer index `w`, the lattice `3^j q ℤ^d` of such
centers, and the cell at an index.  Nothing here depends on `q` being a rounded grid; the
printed hypothesis `q = 𝒬(𝔪)` stays with the consumer, exactly as it does in
`HCPoly/Entry/Geometry/AdaptedCell.lean`.

The aligned notions rest on `adaptedCell` and `adaptedCellTranslate` from
`HCPoly/Setup/Geometry.lean` and `adaptedCellCenter` from `HCPoly/Setup/Moments.lean`.

`adaptedCellCenter` is the center `3^j q w` of the cell at the integer index `w`, and
`adaptedCellAtCenter` is the translate of that cell, defined through `adaptedCellTranslate`.
`adaptedLatticeAtScale` is the scaled lattice `3^j q ℤ^d`, not `q ℤ^d`: the generation `j` is a
parameter here, and every printed use is of the scaled lattice.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- The aligned lattice `3^j q ℤ^d` of cell centres at scale `j`.

This is not the `adaptedLattice` of the published `HCPoly` library
(`HCPoly/Setup/Geometry.lean`), which takes no scale argument and is the unscaled lattice
`q ℤ^d`.  `adaptedLatticeAtScale q j` is the image of that lattice under `x ↦ 3^j x`, so the
two agree only at `j = 0`. -/
@[expose]
def adaptedLatticeAtScale (q : Mat d) (j : ℤ) : Set (Vec d) :=
  Set.range (adaptedCellCenter q j)

/-- The aligned adapted cell `z + ⋄_j^q` at the integer index `w`, i.e. at the centre
`z = 3^j q w ∈ 3^j q ℤ^d`, written as the translate of `⋄_j^q` by that centre.

The `adaptedCellAt` of the published `HCPoly` library (`HCPoly/Setup/Geometry.lean`) is the
same set of points, written directly as the image of `adaptedCell q j` under `x ↦ 3^j q w + x`.
The two are equal by unfolding `adaptedCellTranslate` and `adaptedCellCenter`, but neither is
the other's normal form, so a `simp` or `rw` lemma about one does not fire on the other. -/
@[expose]
def adaptedCellAtCenter (q : Mat d) (j : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  adaptedCellTranslate q j (adaptedCellCenter q j w)

end

end HCPolySupport.HighContrast
end

section
/-!
## The fixed moment `Q` and the exponent `ρ_max`

`e.scale.selection.Q.choice`:

> Fix the even moment and set
> `Q := 2⌈2(d+1)/(1-γ)⌉` and `ρ_max := γ + (1/Q)(d + ¼(1-γ)) < 1`.

Both are formulas in the dimension `d` and the coarse-ellipticity exponent `γ`, and both
match the printed display symbol for symbol.  Two things the display asserts are **not**
part of either definition and are not asserted here: that `ρ_max < 1`, and that `Q` is even
(it is `2` times a natural number by construction).  Each is a statement about these values
and is proved separately.

`⌈·⌉` is the ceiling into `ℕ`, so `Q : ℕ`: the print uses `Q` as a moment order and compares
it with integers (`h ≥ 2Q`).  For `γ ∈ [0,1)` — the standing range of the coarse-ellipticity
exponent — the argument `2(d+1)/(1-γ)` is positive and the ceiling into `ℕ` agrees with the
ceiling into `ℤ`.  Outside that range, `1 - γ ≤ 0` makes the quotient nonpositive or
undefined, but `Q` need not vanish; the printed hypothesis `γ ∈ [0,1)` stays with the
consumer.  The resulting totalized values have no printed interpretation outside that range.

The `¼(1-γ)` and `⅛(1-γ)` that appear in the histories, the drift and the profile are
written out at their use sites, exactly as the print does; the print gives them no name and
none is introduced here.

Equivalently, `ρ_max = γ + (d + a)/Q` with `a = ¼(1-γ)`; no symbol for this additive
exponent, and no separate exponent for the drift, occurs in the paper.
-/

namespace HCPolySupport.HighContrast

noncomputable section

/-- The fixed even moment `Q = 2⌈2(d+1)/(1-γ)⌉` of `e.scale.selection.Q.choice`. -/
@[expose]
def bigQ (d : ℕ) (γ : ℝ) : ℕ :=
  2 * ⌈2 * ((d : ℝ) + 1) / (1 - γ)⌉₊

/-- The exponent `ρ_max = γ + (1/Q)(d + ¼(1-γ))` of `e.scale.selection.Q.choice`. -/
@[expose]
def rhoMax (d : ℕ) (γ : ℝ) : ℝ :=
  γ + (bigQ d γ : ℝ)⁻¹ * ((d : ℝ) + (1 - γ) / 4)

end

end HCPolySupport.HighContrast
end

section
/-!
## The adapted-grid Whitney families of the two-grid lemma

`l.two.grid.whitney`, the two constructions:

> (i) Let `W = y + ⋄_j^{q'}`, with `y ∈ 3^j q' ℤ^d`.  Select the maximal adapted cubes of
> the `q`-grid contained in `W` whose generations are at most `j − ℓ`.  Denote their centers
> at generation `r` by `𝒵_r(W)`. …
> (ii) Let `W = y + ⋄_j^q`, with `y ∈ 3^j q ℤ^d`.  First take all the adapted cubes
> `z + ⋄_{j−ℓ}^{q'}`, with `z ∈ 3^{j−ℓ} q' ℤ^d`, contained in `W`.  In the uncovered part,
> select the maximal adapted cubes of the `q`-grid whose generations are at most `j − ℓ`,
> and again denote their centers by `𝒵_r(W)`.

`HCPoly/Entry/Geometry/MaximalCells.lean` has exactly this family for the **standard** cubes
`standardCell d k w`, as `IsCellIn`, `IsMaximalCellIn`, `maximalCellIndices`,
`maximalCellPairs`.  This file is that file's four definitions for the **adapted** cells
`adaptedCellAtCenter q r w` of a grid `q`, together with the covered and uncovered parts that
construction (ii) needs.  The definitions are deliberately the same shape, so that the two
families can be compared declaration by declaration.

What is in the print and *not* here, because it is a statement and not a definition: that
the selected cubes partition `W` up to a null set; the three counts of
`e.two.grid.whitney.counts`; and the two volume identities of
`e.two.grid.whitney.volumes`.  In particular the print's `#𝒵_r(W)` presupposes the family to
be finite, which is part of what the lemma asserts; the family is a `Set` here, and a
statement about its cardinality is written with `Set.ncard` or by exhibiting a `Finset`.

Both constructions take the generation bound `j − ℓ` as a single argument: nothing here
depends on how it is composed, and the printed hypotheses (`W` a cell of the other grid,
`y` aligned, `ℓ ≥ 1`, `K(q,q') ≤ K_0`) stay with the consumer.

-/

open HCPolySupport.HighContrast (adaptedCellCenter)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- `adaptedCellAtCenter q r w` is a member of the family: generation at most `j` and contained in
`W`.  The adapted-grid analogue of `Geometry.IsCellIn`. -/
@[expose]
def IsAdaptedCellIn (W : Set (Vec d)) (q : Mat d) (j r : ℤ) (w : Fin d → ℤ) : Prop :=
  r ≤ j ∧ adaptedCellAtCenter q r w ⊆ W

/-- `adaptedCellAtCenter q r w` is a maximal member of the family of adapted cells of the `q`-grid
contained in `W` with generation at most `j`: it belongs to the family and every member
containing it is equal to it.  The adapted-grid analogue of `Geometry.IsMaximalCellIn`. -/
@[expose]
def IsMaximalAdaptedCellIn (W : Set (Vec d)) (q : Mat d) (j r : ℤ) (w : Fin d → ℤ) : Prop :=
  IsAdaptedCellIn W q j r w ∧
    ∀ r' w', IsAdaptedCellIn W q j r' w' → adaptedCellAtCenter q r w ⊆ adaptedCellAtCenter q r' w' →
      adaptedCellAtCenter q r' w' = adaptedCellAtCenter q r w

/-- The indices `w` of the maximal adapted cells at generation `r`. -/
@[expose]
def maximalAdaptedCellIndices (W : Set (Vec d)) (q : Mat d) (j r : ℤ) : Set (Fin d → ℤ) :=
  {w | IsMaximalAdaptedCellIn W q j r w}

/-- The centers `𝒵_r(W)` of the maximal adapted cells at generation `r`: the points
`3^r q w ∈ 3^r q ℤ^d` at which those cells sit. -/
@[expose]
def maximalAdaptedCellCenters (W : Set (Vec d)) (q : Mat d) (j r : ℤ) : Set (Vec d) :=
  adaptedCellCenter q r '' maximalAdaptedCellIndices W q j r

/-- The part of `W` covered by the adapted cells of the grid `q` at generation `j` that are
contained in `W`: the first family of construction (ii), taken at `q = q'` and
`j = j − ℓ`. -/
@[expose]
def adaptedCoveredPart (W : Set (Vec d)) (q : Mat d) (j : ℤ) : Set (Vec d) :=
  ⋃ w ∈ {w : Fin d → ℤ | adaptedCellAtCenter q j w ⊆ W}, adaptedCellAtCenter q j w

/-- The uncovered part of `W`: what is left of `W` after the adapted cells of the grid `q`
at generation `j` contained in `W` are removed.  Construction (ii) selects its maximal
adapted cells of the other grid. -/
@[expose]
def adaptedUncoveredPart (W : Set (Vec d)) (q : Mat d) (j : ℤ) : Set (Vec d) :=
  W \ adaptedCoveredPart W q j

end

end HCPolySupport.HighContrast
end
