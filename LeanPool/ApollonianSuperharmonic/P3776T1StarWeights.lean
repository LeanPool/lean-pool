/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1OpenStar
public import LeanPool.ApollonianSuperharmonic.StandardSimplex

/-!
# P3776T1StarWeights

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

-- [TABLET NODE: P3776T1StarWeights]
/--
For $P$, star coordinates are continuous real functions $w_a$ on the
plane, nonnegative and positive exactly on $U_a$ of
`P3776T1OpenStar`. On every closed face region the three
functions at its numbered vertices form a point of the standard
two-simplex. On the arc $ab$ all functions other than $w_a,w_b$ vanish;
at the position of $b$, $w_a$ is $1$ if $a=b$ and $0$ otherwise.
They satisfy $w_{u+a}(x+[u])=w_a(x)$ for every lattice translation.
-/
structure P3776T1StarWeights {ι : Type} (P : PeriodicTileCore ι) where
-- BODY
  /-- The nonnegative continuous barycentric weight supported on each open vertex star. -/
  weight : ι → (Real × Real) → Real
  continuous : ∀ a, Continuous (weight a)
  nonnegative : ∀ a x, 0 ≤ weight a x
  positive_iff : ∀ a x, 0 < weight a x ↔ x ∈ P3776T1OpenStar P a
  face_simplex : ∀ f x, x ∈ closure (P.plane.faceRegion f) →
    (fun i => weight (P.plane.faceVertex f i) x) ∈ StandardSimplex (Fin 3)
  edge_support : ∀ a b, P.plane.adjacent a b → ∀ x,
    x ∈ P.plane.edgeArc a b → ∀ c, c ≠ a → c ≠ b → weight c x = 0
  vertex_value : ∀ a b,
    weight a (P.plane.position b) =
      @ite Real (a = b) (Classical.propDecidable _) 1 0
  periodic : ∀ u : P.lattice, ∀ a x,
    weight (P.shift u a) (x + GaussianRealPoint u) = weight a x

end ApollonianSuperharmonic

end
