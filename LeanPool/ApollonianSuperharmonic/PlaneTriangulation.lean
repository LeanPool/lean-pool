/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: PlaneTriangulation]

/-!
# PlaneTriangulation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A locally finite, $3$-connected cellular plane triangulation consists of a
simple locally finite graph, triangular faces with every edge incident to
exactly two distinct faces, and a cellular embedding in $\mathbb R^2$.
The two faces are given without an ordering: every other face incident to
that edge is one of them.  The embedding records distinct vertex positions
and, for every adjacent pair, an arc homeomorphic to $[0,1]$ whose two
endpoints are the two vertex positions.  Distinct edge arcs are disjoint when
their edges are disjoint and otherwise meet exactly at their common endpoint.
It also records pairwise-disjoint open connected face regions whose frontiers
are exactly the three incident arcs and whose vertices, arcs, and regions
cover the plane.  Three-connectivity means that deleting any set of fewer
than three vertices leaves a path between any two remaining vertices.
-/
structure PlaneTriangulation (ι : Type) where
-- BODY
  /-- The simple locally finite graph adjacency relation. -/
  adjacent : ι → ι → Prop
  /-- The type of triangular face labels of the fixed cellular embedding. -/
  Face : Type
  /-- The three numbered graph vertices of each face. -/
  faceVertex : Face → Fin 3 → ι
  /-- The injective plane position of each graph vertex. -/
  position : ι → Real × Real
  /-- The symmetric embedded arc on each graph edge. -/
  edgeArc : ι → ι → Set (Real × Real)
  /-- The open connected region enclosed by the three arcs of each face. -/
  faceRegion : Face → Set (Real × Real)
  adjacent_symmetric : ∀ a b, adjacent a b ↔ adjacent b a
  adjacent_irreflexive : ∀ a, ¬ adjacent a a
  locally_finite : ∀ a, Set.Finite {b | adjacent a b}
  three_connected : ∀ (D : Finset ι), D.card < 3 →
    ∀ a ∉ D, ∀ b ∉ D, ∃ p : List ι,
      p.head? = some a ∧ p.getLast? = some b ∧
      (∀ x ∈ p, x ∉ D) ∧
      ∀ x y : ι, ∀ l₁ l₂ : List ι,
        p = l₁ ++ x :: y :: l₂ → adjacent x y
  face_vertices_distinct : ∀ f, Function.Injective (faceVertex f)
  face_edges : ∀ f i j, i ≠ j → adjacent (faceVertex f i) (faceVertex f j)
  every_edge_two_faces : ∀ a b, adjacent a b →
    ∃ f g : Face, f ≠ g ∧
      ((∃ i, faceVertex f i = a) ∧ (∃ i, faceVertex f i = b)) ∧
      ((∃ i, faceVertex g i = a) ∧ (∃ i, faceVertex g i = b)) ∧
      ∀ h : Face,
        ((∃ i, faceVertex h i = a) ∧ (∃ i, faceVertex h i = b)) →
          h = f ∨ h = g
  position_injective : Function.Injective position
  arc_symmetric : ∀ a b, edgeArc a b = edgeArc b a
  arc_homeomorph : ∀ a b, adjacent a b →
    ∃ h : (Set.Icc (0 : Real) 1) ≃ₜ edgeArc a b,
      ((h ⟨0, by norm_num⟩ : edgeArc a b) : Real × Real) = position a ∧
      ((h ⟨1, by norm_num⟩ : edgeArc a b) : Real × Real) = position b
  arc_intersections : ∀ a b c d, adjacent a b → adjacent c d →
    ({a, b} : Set ι) ≠ ({c, d} : Set ι) →
      edgeArc a b ∩ edgeArc c d =
        position '' (({a, b} : Set ι) ∩ ({c, d} : Set ι))
  region_open : ∀ f, IsOpen (faceRegion f)
  region_connected : ∀ f, IsConnected (faceRegion f)
  region_disjoint : Pairwise fun f g => Disjoint (faceRegion f) (faceRegion g)
  face_boundary : ∀ f,
    frontier (faceRegion f) =
      edgeArc (faceVertex f 0) (faceVertex f 1) ∪
      edgeArc (faceVertex f 1) (faceVertex f 2) ∪
      edgeArc (faceVertex f 2) (faceVertex f 0)
  plane_cover : Set.range position ∪
      {p | ∃ a b, adjacent a b ∧ p ∈ edgeArc a b} ∪
      {p | ∃ f, p ∈ faceRegion f} = Set.univ

end ApollonianSuperharmonic

end
