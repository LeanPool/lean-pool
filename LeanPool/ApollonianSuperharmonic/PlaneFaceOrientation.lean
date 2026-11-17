/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation

-- [TABLET NODE: PlaneFaceOrientation]

/-!
# PlaneFaceOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $G$ be a locally finite cellular plane triangulation.  A coherent
orientation of its face sides chooses, for every directed graph edge
$a b$, one of the two incident faces, denoted $L(a,b)$.  The chosen face
contains both endpoints, $L(a,b)\ne L(b,a)$, and these two faces exhaust
the faces incident to the unoriented edge $\{a,b\}$.  The choices are
coherent when the three directed boundary edges of every triangular face
can be cyclically ordered so that the face lies on the chosen left side of
all three.  Reversing every directed edge produces the global opposite
convention; the definition does not impose an orientation on the
arbitrary stored numbering of the three vertices of a face.
-/
structure PlaneFaceOrientation {ι : Type} (G : PlaneTriangulation ι) where
-- BODY
  /-- The coherently selected incident face to the left of each directed edge. -/
  leftFace : ι → ι → G.Face
  left_incident : ∀ a b, G.adjacent a b →
    (∃ i, G.faceVertex (leftFace a b) i = a) ∧
      (∃ i, G.faceVertex (leftFace a b) i = b)
  opposite_sides : ∀ a b, G.adjacent a b →
    leftFace a b ≠ leftFace b a
  sides_exhaust_faces : ∀ a b, G.adjacent a b → ∀ f : G.Face,
    ((∃ i, G.faceVertex f i = a) ∧ (∃ i, G.faceVertex f i = b)) →
      f = leftFace a b ∨ f = leftFace b a
  coherently_oriented : ∀ f : G.Face, ∃ σ : Equiv.Perm (Fin 3),
    leftFace (G.faceVertex f (σ 0)) (G.faceVertex f (σ 1)) = f ∧
      leftFace (G.faceVertex f (σ 1)) (G.faceVertex f (σ 2)) = f ∧
      leftFace (G.faceVertex f (σ 2)) (G.faceVertex f (σ 0)) = f

end ApollonianSuperharmonic

end
