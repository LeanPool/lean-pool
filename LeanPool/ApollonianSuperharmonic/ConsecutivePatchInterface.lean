/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FiniteInducedTilePatch

-- [TABLET NODE: ConsecutivePatchInterface]

/-!
# ConsecutivePatchInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $K$ be a finite induced tile patch and let $d\notin K$.  A
\emph{consecutive patch interface at $d$} is a positive-length injective
list of precisely those neighbors of $d$ which lie in $K$, together with an
injective list of one more triangular face, such that the $k$-th neighbor
and $d$ are both vertices of the $k$-th and $(k+1)$-st listed faces.  Thus
the edges from $d$ into $K$ form one consecutive interval in the cyclic
link of $d$, and the two end faces are retained explicitly.
-/
structure ConsecutivePatchInterface {ι : Type}
    (G : PlaneTriangulation ι) (tile : ι → ProtoTile)
    (K : FiniteInducedTilePatch G tile) (d : ι) where
-- BODY
  exterior : d ∉ K.indices
  /-- The number of consecutive neighbors in the patch-facing interval. -/
  length : Nat
  positive : 0 < length
  /-- The ordered patch neighbors along the link of the exterior tile. -/
  neighbor : Fin length → ι
  /-- The consecutive incident faces, including the two end faces. -/
  face : Fin (length + 1) → G.Face
  neighbor_injective : Function.Injective neighbor
  face_injective : Function.Injective face
  neighbors_exact : ∀ b, b ∈ K.indices ∧ G.adjacent d b ↔
    ∃ k, neighbor k = b
  consecutive_faces : ∀ k,
    (∃ i, G.faceVertex (face (Fin.castSucc k)) i = d) ∧
    (∃ i, G.faceVertex (face (Fin.castSucc k)) i = neighbor k) ∧
    (∃ i, G.faceVertex (face k.succ) i = d) ∧
    (∃ i, G.faceVertex (face k.succ) i = neighbor k)

end ApollonianSuperharmonic

end
