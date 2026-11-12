/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileContactRouting
public import LeanPool.ApollonianSuperharmonic.PlaneFaceOrientation

-- [TABLET NODE: PlaneEmbeddingAgreement]

/-!
# PlaneEmbeddingAgreement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $P$ be a periodic tile complex and let $R$ be a
`PeriodicTileContactRouting`.  A plane-embedding agreement records
the geometric side components and the induced rotation system of $R$, and
compares them with the fixed cellular embedding of $P$.

More precisely, it chooses a coherent fixed-face orientation in the sense
of `PlaneFaceOrientation`.  For each directed prescribed edge
$ab$, it chooses one of its two fixed incident faces, denoted
$F_R(a,b)$, and the corresponding open connected component $S_R(a,b)$ of
the complement of the routed vertices and arcs.  The full routed arc
$A_{ab}$ lies in the frontier of both $S_R(a,b)$ and $S_R(b,a)$; these two
components are disjoint.  Component means maximal open connected subset of
the drawing complement.  The two labels $F_R(a,b)$ and $F_R(b,a)$ are
distinct and exhaust the two fixed faces incident to $ab$, and directed
edges labeled by the same fixed face select the same complementary
component.  Consequently the labels describe the cyclic order actually
induced by the routed arcs, rather than an independently stored abstract
order.

One Boolean records the single global orientation choice.  Simultaneously
for every directed edge, $F_R(a,b)$ is the fixed left face of $ab$ when
the Boolean is false and the fixed left face of $ba$ when it is true.
Thus the two fixed incident faces are individually identified with the two
geometric sides of every routed edge, up to one global reversal.  No
ambient homeomorphism and no exact transport of the fixed face regions is
part of the agreement.
-/
structure PlaneEmbeddingAgreement {ι : Type}
    (P : PeriodicTileComplex ι) (R : PeriodicTileContactRouting P) where
-- BODY
  /-- The coherent orientation of the fixed face sides. -/
  fixedOrientation : PlaneFaceOrientation P.plane
  /-- The fixed face label occupying the selected geometric side of a routed directed edge. -/
  routedLeftFace : ι → ι → P.plane.Face
  /-- The maximal open complementary component on that routed directed side. -/
  routedLeftSide : ι → ι → Set (Real × Real)
  /-- The single global choice comparing the routed and fixed orientations. -/
  reversed : Bool
  routed_left_incident : ∀ a b, P.plane.adjacent a b →
    (∃ i, P.plane.faceVertex (routedLeftFace a b) i = a) ∧
      (∃ i, P.plane.faceVertex (routedLeftFace a b) i = b)
  routed_opposite_faces : ∀ a b, P.plane.adjacent a b →
    routedLeftFace a b ≠ routedLeftFace b a
  routed_sides_exhaust_faces : ∀ a b, P.plane.adjacent a b →
    ∀ f : P.plane.Face,
      ((∃ i, P.plane.faceVertex f i = a) ∧
        (∃ i, P.plane.faceVertex f i = b)) →
        f = routedLeftFace a b ∨ f = routedLeftFace b a
  routed_side_open : ∀ a b, P.plane.adjacent a b →
    IsOpen (routedLeftSide a b)
  routed_side_connected : ∀ a b, P.plane.adjacent a b →
    IsConnected (routedLeftSide a b)
  routed_side_avoids_drawing : ∀ a b, P.plane.adjacent a b →
    Disjoint (routedLeftSide a b)
      (Set.range R.position ∪
        {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ R.edgeArc c d})
  routed_edge_in_side_frontiers : ∀ a b, P.plane.adjacent a b →
    R.edgeArc a b ⊆
      frontier (routedLeftSide a b) ∩ frontier (routedLeftSide b a)
  routed_opposite_sides : ∀ a b, P.plane.adjacent a b →
    Disjoint (routedLeftSide a b) (routedLeftSide b a)
  routed_side_component : ∀ a b, P.plane.adjacent a b →
    ∀ U : Set (Real × Real), IsOpen U → IsConnected U →
      Disjoint U
        (Set.range R.position ∪
          {p | ∃ c d, P.plane.adjacent c d ∧ p ∈ R.edgeArc c d}) →
      (U ∩ routedLeftSide a b).Nonempty → U ⊆ routedLeftSide a b
  same_face_same_side : ∀ a b c d,
    P.plane.adjacent a b → P.plane.adjacent c d →
    routedLeftFace a b = routedLeftFace c d →
      routedLeftSide a b = routedLeftSide c d
  face_side_agreement : ∀ a b, P.plane.adjacent a b →
    routedLeftFace a b =
      if reversed = true then fixedOrientation.leftFace b a
      else fixedOrientation.leftFace a b

end ApollonianSuperharmonic

end
