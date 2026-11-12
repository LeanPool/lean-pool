/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3475T1TriangleTree
public import LeanPool.ApollonianSuperharmonic.P3511T1SourceConstruction
public import LeanPool.ApollonianSuperharmonic.P3511T1ConvexComparison
public import LeanPool.ApollonianSuperharmonic.P3511T1LeafOrder
public import LeanPool.ApollonianSuperharmonic.P3511T1AttachmentIntersection

-- [TABLET NODE: P3475T1PolygonTriangleConstruction]

/-!
# P3475T1PolygonTriangleConstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3475T1PolygonTriangleConstruction {n : Nat}
    (p : P3381T1PolygonBoundary n)
    (hcorner : ∀ i : Fin (n + 3),
      P3381T1TriangleDeterminant (fun j : Fin 3 =>
        p.vertex (i + ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_left 3 n)⟩)) ≠ 0) :
    ∃ X K : Set (Real × Real), Nonempty (P3475T1TriangleTree p X K) := by
-- BODY
  obtain ⟨X, ⟨s⟩⟩ := P3511T1SourceConstruction p hcorner
  obtain ⟨K, ⟨t⟩⟩ := P3511T1ConvexComparison s
  obtain ⟨order, horder⟩ := P3511T1LeafOrder s
  refine ⟨X, K, ⟨{
    target := t.target
    target_injective := t.target_injective
    target_edge_intersection := t.target_edge_intersection
    count := s.count
    face := s.face
    face_injective := s.face_injective
    face_distinct := s.face_distinct
    vertex_used := s.vertex_used
    source_nondegenerate := s.nondegenerate
    target_nondegenerate := t.target_nondegenerate
    source_cover := s.cover
    target_cover := t.target_cover
    source_intersection := s.intersection
    target_intersection := t.target_intersection
    edge_count := s.edge_count
    target_hull := t.target_hull
    target_convex := t.target_convex
    target_closed := t.target_closed
    target_bounded := t.target_bounded
    target_interior := t.target_interior
    target_frontier := t.target_frontier
    count_pos := s.count_pos
    order := order
    attachment := ?_
  }⟩⟩
  intro k hk
  obtain ⟨a, b, c, hab, hac, hbc, hf, hn, he⟩ := horder k hk
  refine ⟨a, b, c, hab, hac, hbc, hf, hn, he, ?_, ?_⟩
  · exact P3511T1AttachmentIntersection p.vertex s.face s.intersection
      order k a b c hf hn he
  · exact P3511T1AttachmentIntersection t.target s.face t.target_intersection
      order k a b c hf hn he

end ApollonianSuperharmonic

end
