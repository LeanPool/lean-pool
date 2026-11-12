/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3544T1DiagonalSplit
public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCorner
public import LeanPool.ApollonianSuperharmonic.P3650T1VisibleDiagonal
public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildren
public import LeanPool.ApollonianSuperharmonic.P3650T1ExposedCornerExists
public import LeanPool.ApollonianSuperharmonic.P3650T1TriangleEntry
public import LeanPool.ApollonianSuperharmonic.P3650T1EmptyTriangleDiagonal
public import LeanPool.ApollonianSuperharmonic.P3650T1MaximalHeightDiagonal
public import LeanPool.ApollonianSuperharmonic.P3650T1CyclicChildrenExists
public import LeanPool.ApollonianSuperharmonic.P3650T1ParitySum
public import LeanPool.ApollonianSuperharmonic.P3650T1OldArcEven
public import LeanPool.ApollonianSuperharmonic.P3650T1LocalCoherence

-- [TABLET NODE: P3544T1DiagonalSelection]

/-!
# P3544T1DiagonalSelection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3544T1DiagonalSelection {n : Nat} (p : P3381T1PolygonBoundary n)
    (hn : 0 < n) : Nonempty (P3544T1DiagonalSplit p) := by
-- BODY
  classical
  obtain ⟨E⟩ := P3650T1ExposedCornerExists p
  have hentry := P3650T1TriangleEntry p E
  have hvisible : Nonempty (P3650T1VisibleDiagonal p E) := by
    by_cases hempty : ∀ i, p.vertex i ∈ convexHull Real
        ({p.vertex (E.b - 1), p.vertex E.b, p.vertex (E.b + 1)} :
          Set (Real × Real)) → i = E.b - 1 ∨ i = E.b ∨ i = E.b + 1
    · obtain ⟨D, _, _⟩ := P3650T1EmptyTriangleDiagonal p hn E hentry hempty
      exact ⟨D⟩
    · obtain ⟨D, _, _, _⟩ := P3650T1MaximalHeightDiagonal p E hentry hempty
      exact ⟨D⟩
  obtain ⟨D⟩ := hvisible
  obtain ⟨C⟩ := P3650T1CyclicChildrenExists p D.a D.b
    D.distinct D.not_next D.not_previous D.clear
  have hsum := (P3650T1ParitySum p D.a D.b C).2
  obtain ⟨hleft, hright⟩ := P3650T1OldArcEven p E D C
  obtain ⟨hsides, hendpoints⟩ := P3650T1LocalCoherence p D.a D.b D.distinct C
    D.odd hleft hright hsum
  exact ⟨{
    left_n := C.left_n
    right_n := C.right_n
    left_lt := C.left_lt
    right_lt := C.right_lt
    left := C.left
    right := C.right
    il := C.il
    ir := C.ir
    il_injective := C.il_injective
    ir_injective := C.ir_injective
    left_vertex := C.left_vertex
    right_vertex := C.right_vertex
    a := D.a
    b := D.b
    a_ne_b := D.distinct
    u := C.u
    v := C.v
    hu := C.hu
    hv := C.hv
    rotation := C.rotation
    parent_order := C.parent_order
    left_order := C.left_order
    right_order := C.right_order
    common_indices := C.common_indices
    carrier_union := C.carrier_union
    carrier_intersection := C.carrier_intersection
    diagonal_odd := D.odd
    left_arc_even := hleft
    right_arc_even := hright
    parity_sum := hsum
    diagonal_sides := hsides
    endpoint_coherence := hendpoints }⟩

end ApollonianSuperharmonic

end
