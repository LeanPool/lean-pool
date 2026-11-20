/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Nopert
public import LeanPool.RupertMinimality.Minimality.SixClass
public import LeanPool.RupertMinimality.Minimality.Planar

/-!
# Every nopert has at least 7 points

A convex polyhedron is *Rupert* if a copy of it can pass through a straight
hole cut in another copy of the same size (`IsRupert`, `MainTheorem.lean`:
some view of the polyhedron, possibly shifted, fits strictly inside the
shadow of another view).  A *nopert* is a solid convex polyhedron that is not
Rupert (`IsNopert`, `Nopert.lean`).  Polyhedra are given by finite sets
`V : Finset ℝ³` of points; the polyhedron is their convex hull.

The `Minimality/` modules prove the geometric cases and their classification.

* `seven_le_card_of_isNopert`: every nopert has at least 7 points.  This
  follows from `isRupert_of_card_le_six`: every solid convex polyhedron
  given by at most 6 points is Rupert.
* For flat point sets the answer is known for any number of points: points in
  a plane, not all on one line, are Rupert
  (`isRupert_of_coplanar_of_not_collinear`), while points on one line are not
  (`not_isRupert_of_collinear`).  Hence `isRupert_iff_of_card_le_six`:
  at most 6 points are Rupert exactly when they are not all on one line (or
  there are none at all).

All results depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

@[expose] public section

namespace RupertMinimality

/-- **Every solid convex polyhedron with at most 6 vertices is Rupert.**
More precisely: at most 6 points of `ℝ³`, not all in one plane, have a Rupert
convex hull.  (The points need not all be vertices of the hull.) -/
theorem isRupert_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6)
    (hsolid : ¬ Coplanar ℝ (V : Set ℝ³)) : IsRupert V :=
  Minimality.isRupert_of_card_le_six V hV
    ((not_coplanar_iff_interior_convexHull_nonempty _).mp hsolid)

/-- **Every nopert has at least 7 points** (hence at least 7 vertices: its
vertex set has the same convex hull, so is a nopert too). -/
theorem seven_le_card_of_isNopert (V : Finset ℝ³) (h : IsNopert V) : 7 ≤ V.card := by
  by_contra hlt
  exact h.2 (isRupert_of_card_le_six V (by omega) h.1)

/-- **Flat polygons are Rupert.**  Points in a plane, not all on one line, are
Rupert, whatever their number: hold one copy face-on and pass the other
through it edge-on. -/
theorem isRupert_of_coplanar_of_not_collinear (V : Finset ℝ³)
    (hpl : Coplanar ℝ (V : Set ℝ³)) (hcol : ¬ Collinear ℝ (V : Set ℝ³)) : IsRupert V :=
  Minimality.isRupert_of_coplanar_of_not_collinear V hpl hcol

/-- **Segments and points are not Rupert.**  A nonempty set of points on one
line is not Rupert: all its shadows lie on lines, so they have no interior. -/
theorem not_isRupert_of_collinear (V : Finset ℝ³) (h : Collinear ℝ (V : Set ℝ³))
    (hne : V.Nonempty) : ¬ IsRupert V :=
  Minimality.not_isRupert_of_collinear V h hne

/-- **At most 6 points: exactly the non-collinear sets are Rupert** (and the
empty set, vacuously). -/
theorem isRupert_iff_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6) :
    IsRupert V ↔ (V = ∅ ∨ ¬ Collinear ℝ (V : Set ℝ³)) := by
  constructor
  · intro hR
    by_contra hcon
    push Not at hcon
    exact not_isRupert_of_collinear V hcon.2 hcon.1 hR
  · rintro (rfl | hcol)
    · exact Minimality.isRupert_empty
    · by_cases hpl : Coplanar ℝ (V : Set ℝ³)
      · exact isRupert_of_coplanar_of_not_collinear V hpl hcol
      · exact isRupert_of_card_le_six V hV hpl

/-- The six-point result in the indexed form used by the existing Rupert library. -/
theorem indexed_isRupert_of_card_le_six (vertices : Finset ℝ³) (hcard : vertices.card ≤ 6)
    (hsolid : ¬ Coplanar ℝ (vertices : Set ℝ³)) :
    _root_.IsRupert (fun v : vertices => v.val) :=
  (isRupert_finset_iff_indexed vertices).mp (isRupert_of_card_le_six vertices hcard hsolid)

end RupertMinimality
