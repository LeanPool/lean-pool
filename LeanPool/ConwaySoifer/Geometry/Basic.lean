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
The point `(a, b)` represents `(a+b/2, sqrt(3)*b/2)` in the Euclidean plane.
The product norm on `Real × Real` is deliberately NOT used for lengths.
All triangles below include their boundary and interior. Degenerate triangles
are allowed, so the eventual statement also includes common side zero.
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
namespace ConwaySoifer
/-- Planar coordinates; Euclidean lengths use the quadratic form described in this module. -/
abbrev Point := ℝ × ℝ

/-- Squared Euclidean distance in the coordinate system described in this module. -/
def sqDist (p q : Point) : ℝ :=
  (p.1-q.1) ^ 2 + (p.1-q.1)*(p.2-q.2) + (p.2-q.2) ^ 2

/-- The filled equilateral target of side three in triangular coordinates. -/
def target : Set Point := {p | p.1 ≤ 1 ∧ p.2 ≤ 1 ∧ -1 ≤ p.1+p.2}
/-- The closed central unit hexagon in triangular coordinates. -/
def hexagon : Set Point := {p | |p.1| ≤ 1 ∧ |p.2| ≤ 1 ∧ |p.1+p.2| ≤ 1}
/-- The six cyclic vertices of the unit hexagon. -/
def vertex : Fin 6 → Point := ![(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
/-- The three vertices of the side-three target. -/
def corner : Fin 3 → Point := ![(1, 1), (-2, 1), (1, -2)]
/-- The centre and boundary vertices used to assign distinct covering owners. -/
def anchor : Fin 10 → Point :=
  ![(0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1), (1, 1), (-2, 1), (1, -2)]

/-- Three equidistant vertices with a nonnegative side length; the carrier is their closed hull. -/
structure EquilateralTriangle where
  /-- The three triangle vertices. -/
  vertices : Fin 3 → Point
  /-- The common side length. -/
  side : ℝ
  side_nonneg : 0 ≤ side
  equilateral : ∀ i j, i ≠ j → sqDist (vertices i) (vertices j) = side ^ 2

/-- The filled closed convex hull of the three triangle vertices. -/
def EquilateralTriangle.carrier (T : EquilateralTriangle) : Set Point :=
  convexHull ℝ (Set.range T.vertices)
/-- The finite family of covering triangles used by this module. -/
abbrev Configuration := Fin 10 → EquilateralTriangle
/-- Every point of the side-three target lies in at least one covering triangle. -/
def Covers (T : Configuration) : Prop := ∀ p ∈ target, ∃ i, p ∈ (T i).carrier
/-- Every covering triangle has the specified common side length. -/
def CommonSide (T : Configuration) (r : ℝ) : Prop := ∀ i, (T i).side = r

/-- This is the actual target proposition, not a claim that it has been proved. -/
def LowerBound : Prop := ∀ (r : ℝ) (T : Configuration), CommonSide T r → Covers T → 1 ≤ r

/-- No equilateral triangle of side below one contains the given set. -/
def ExcludesSubunit (S : Set Point) : Prop :=
  ∀ T : EquilateralTriangle, T.side < 1 → ¬ S ⊆ T.carrier

theorem sqDist_nonneg (p q : Point) : 0 ≤ sqDist p q := by
  unfold sqDist
  nlinarith [sq_nonneg (2*(p.1-q.1)+(p.2-q.2)), sq_nonneg (p.2-q.2)]
theorem sqDist_comm (p q : Point) : sqDist p q = sqDist q p := by
  unfold sqDist; ring

theorem sqDist_smul (a : ℝ) (p q : Point) :
    sqDist (a • p) (a • q) = a ^ 2 * sqDist p q := by
  rcases p with ⟨x, y⟩; rcases q with ⟨z, w⟩
  dsimp [sqDist]; ring

/-- Conversion to the oblique coordinates of the upstream SevenTriangles library. -/
def toOblique (p : Point) : Point := (p.1 + p.2/2, p.2)
theorem sqDist_toOblique (p q : Point) :
    ((toOblique p).1-(toOblique q).1) ^ 2 +
      (3/4 : ℝ)*((toOblique p).2-(toOblique q).2) ^ 2 = sqDist p q := by
  dsimp [sqDist, toOblique]; ring

theorem hexagon_subset_target : hexagon ⊆ target := by
  intro p hp
  rcases hp with ⟨ha, hb, hc⟩
  exact ⟨(abs_le.mp ha).2, (abs_le.mp hb).2, (abs_le.mp hc).1⟩
theorem anchor_mem_target (i : Fin 10) : anchor i ∈ target := by
  fin_cases i <;> norm_num [anchor, target]
theorem anchors_separated (i j : Fin 10) (h : i ≠ j) : 1 ≤ sqDist (anchor i) (anchor j) := by
  fin_cases i <;> fin_cases j <;> norm_num [anchor, sqDist] at *

/-- Sanity check: the target is the filled equilateral triangle of side three. -/
def targetTriangle : EquilateralTriangle where
  vertices := corner
  side := 3
  side_nonneg := by
    norm_num
  equilateral := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [corner, sqDist] at *
end ConwaySoifer
