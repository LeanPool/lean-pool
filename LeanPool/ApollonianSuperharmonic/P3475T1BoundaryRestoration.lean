/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3475T1BoundarySubdivision
public import LeanPool.ApollonianSuperharmonic.P3475T1TriangleTree
public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionGeometry

-- [TABLET NODE: P3475T1BoundaryRestoration]

/-!
# P3475T1BoundaryRestoration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3475T1BoundaryRestoration {r n : Nat}
    (q : P3381T1PolygonBoundary r) (p : P3381T1PolygonBoundary n)
    (s : P3475T1BoundarySubdivision q p)
    (X K : Set (Real × Real)) (t : P3475T1TriangleTree q X K) :
    Nonempty (P3381T1PairedTriangulation p X K) := by
-- BODY
  classical
  let c := P3523T1InsertionConstruction s t
  let fs := c.faces c.steps.length
  let f := P3523T1FaceEnumeration fs
  let Q := P3523T1InterpolatedTarget s t
  obtain ⟨_, _, hf, hdistinct, hused, hcount, _⟩ :=
    P3523T1InsertionIncidence q p s X K t
  obtain ⟨hsn, htn, hsc, htc, hsi, hti⟩ :=
    P3523T1InsertionGeometry q p s X K t
  obtain ⟨hinj, hedge, hfront⟩ := P3523T1TargetBoundary q p s X K t
  refine ⟨{
    target := Q
    target_injective := hinj
    target_edge_intersection := hedge
    count := fs.card
    face := f
    face_injective := hf
    face_distinct := hdistinct
    vertex_used := hused
    source_nondegenerate := hsn
    target_nondegenerate := htn
    source_cover := hsc
    target_cover := htc
    source_intersection := hsi
    target_intersection := hti
    edge_count := hcount
    target_hull := (P3523T1TargetHull s t).2
    target_convex := t.target_convex
    target_closed := t.target_closed
    target_bounded := t.target_bounded
    target_interior := t.target_interior
    target_frontier := hfront }⟩

end ApollonianSuperharmonic

end
