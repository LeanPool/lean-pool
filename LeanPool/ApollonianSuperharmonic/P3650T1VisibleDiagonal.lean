/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCorner
public import Mathlib.Analysis.Convex.Hull

-- [TABLET NODE: P3650T1VisibleDiagonal]

/-!
# P3650T1VisibleDiagonal

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For $p$ and exposed-corner data $E$ of `P3650T1ExposedCorner`,
this record consists of distinct, nonneighboring cyclic indices $A,B$.
The open segment $(p_A,p_B)$ is disjoint from the parent carrier of
`P3544T1BoundaryCarrier` and contained in its odd set of
`P3544T1RayParity`. One of the following routes is recorded.
In the base route, $A=E.b-1$, $B=E.b+1$, and the closed triangle
$\Delta=\operatorname{conv}\{p_{E.b-1},p_{E.b},p_{E.b+1}\}$ contains
no indexed vertex other than these three. In the top route,
$A=E.b$, $B\ne E.b-1,E.b+1$, and $p_B\in\Delta$.
No child boundary or child parity is part of these data.
-/
structure P3650T1VisibleDiagonal {n : Nat} (p : P3381T1PolygonBoundary n)
    (E : P3650T1ExposedCorner p) where
-- BODY
  /-- The first original boundary label of the visible interior diagonal. -/
  a : Fin (n + 3)
  /-- The second original boundary label of that diagonal. -/
  b : Fin (n + 3)
  distinct : a ≠ b
  not_next : b ≠ a + 1
  not_previous : a ≠ b + 1
  clear : Disjoint (openSegment Real (p.vertex a) (p.vertex b))
    (P3544T1BoundaryCarrier p)
  odd : openSegment Real (p.vertex a) (p.vertex b) ⊆ P3544T1RayParity p
  route :
    (a = E.b - 1 ∧ b = E.b + 1 ∧
      ∀ i, p.vertex i ∈ convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real)) → i = E.b - 1 ∨ i = E.b ∨ i = E.b + 1) ∨
    (a = E.b ∧ b ≠ E.b - 1 ∧ b ≠ E.b + 1 ∧
      p.vertex b ∈ convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real)))

end ApollonianSuperharmonic

end
