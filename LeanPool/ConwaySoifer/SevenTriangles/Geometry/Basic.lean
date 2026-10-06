/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Rational coordinates for the covering problem

`(x, z)` represents the Euclidean point `(x, sqrt(3)/2 * z)`.
The product norm on `ℝ × ℝ` is NOT the metric used for lengths below.
All metric statements use `sqDist`; convexity is unchanged by this invertible
linear change of coordinates. No geometric theorem is assumed as an axiom.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

noncomputable section

namespace ConwaySoifer.SevenTriangles

/-- Planar coordinates; Euclidean lengths use the quadratic form described in this module. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance in the coordinate system described in this module. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (3 / 4 : ℝ) * (p.2 - q.2) ^ 2

/-- Rotation through 60 degrees in oblique coordinates. -/
def rotate60 (p : Point) : Point :=
  (p.1 / 2 - 3 * p.2 / 4, p.1 + p.2 / 2)

/-- The six cyclic vertices of the unit hexagon. -/
def vertex (i : Fin 6) : Point :=
  ![(1, 0), (1 / 2, 1), (-1 / 2, 1), (-1, 0),
    (-1 / 2, -1), (1 / 2, -1)] i

/-- The closed regular unit hexagon in oblique coordinates. -/
def unitHexagon : Set Point :=
  {p | |p.2| ≤ 1 ∧ |p.1 + p.2 / 2| ≤ 1 ∧ |p.1 - p.2 / 2| ≤ 1}

/-- The preceding vertex index in the cyclic hexagon order. -/
def previous (i : Fin 6) : Fin 6 := i + 5

/-- The following vertex index in the cyclic hexagon order. -/
def next (i : Fin 6) : Fin 6 := i + 1

/-- The affine interpolation along a unit-hexagon edge. -/
def boundaryPoint (i : Fin 6) (t : ℝ) : Point :=
  (1 - t) • vertex i + t • vertex (next i)

/-- A nondegenerate filled equilateral triangle, with an explicit side length. -/
structure EquilateralTriangle where
  /-- The three triangle vertices. -/
  vertices : Fin 3 → Point
  /-- The common side length. -/
  side : ℝ
  side_pos : 0 < side
  equilateral : ∀ i j, i ≠ j → sqDist (vertices i) (vertices j) = side ^ 2

/-- The filled closed convex hull of the three triangle vertices. -/
def EquilateralTriangle.carrier (T : EquilateralTriangle) : Set Point :=
  convexHull ℝ (Set.range T.vertices)

/-- The finite family of covering triangles used by this module. -/
abbrev Configuration := Fin 7 → EquilateralTriangle

/-- Every point of the closed unit hexagon belongs to one of the seven triangles. -/
def CoversUnitHexagon (T : Configuration) : Prop :=
  ∀ p ∈ unitHexagon, ∃ i, p ∈ (T i).carrier

/-- The actual geometric goal. This is a proposition, not a proved theorem. -/
def UnitHexagonLowerBound : Prop :=
  ∀ (r : ℝ) (T : Configuration),
    (∀ i, (T i).side ≤ r) → CoversUnitHexagon T → 1 ≤ r

/-- No equilateral triangle of side below one contains the given set. -/
def ExcludesSubunit (S : Set Point) : Prop :=
  ∀ T : EquilateralTriangle, T.side < 1 → ¬ S ⊆ T.carrier

theorem sqDist_nonneg (p q : Point) : 0 ≤ sqDist p q := by
  unfold sqDist
  positivity

theorem sqDist_comm (p q : Point) : sqDist p q = sqDist q p := by
  unfold sqDist
  ring

theorem rotate60_preserves_sqDist (p q : Point) :
    sqDist (rotate60 p) (rotate60 q) = sqDist p q := by
  rcases p with ⟨x, z⟩
  rcases q with ⟨y, w⟩
  dsimp [sqDist, rotate60]
  ring

theorem sqDist_smul (a : ℝ) (p q : Point) :
    sqDist (a • p) (a • q) = a ^ 2 * sqDist p q := by
  rcases p with ⟨x, z⟩
  rcases q with ⟨y, w⟩
  dsimp [sqDist]
  ring

theorem vertex_mem_hexagon (i : Fin 6) : vertex i ∈ unitHexagon := by
  fin_cases i <;> norm_num [vertex, unitHexagon]

/-- Sanity check: the geometric datatype is inhabited by a standard unit sector. -/
def standardSector : EquilateralTriangle where
  vertices := ![(0, 0), (1, 0), (1 / 2, 1)]
  side := 1
  side_pos := by
    norm_num
  equilateral := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [sqDist] at *

end ConwaySoifer.SevenTriangles
