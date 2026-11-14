/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint

-- [TABLET NODE: OpenLatticeEdge]

/-!
# OpenLatticeEdge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For lattice vertices $x,y\in\mathbb Z[i]$, the open lattice edge
$(x,y)^\circ$ is the set of strict convex combinations
$(1-t)x+ty$ with $0<t<1$, viewed in $\mathbb R^2$.
-/
def OpenLatticeEdge (x y : GaussianInt) : Set (ℝ × ℝ) :=
-- BODY
  {p | ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    p = (1 - t) • GaussianRealPoint x + t • GaussianRealPoint y}

end ApollonianSuperharmonic

end
