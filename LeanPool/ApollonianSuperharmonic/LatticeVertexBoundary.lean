/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: LatticeVertexBoundary]

/-!
# LatticeVertexBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a lattice-vertex set $S\subseteq\mathbb Z^2$, its vertex boundary is
$$
 \partial S=\{x\in S:\text{ some }y\notin S\text{ differs from }x
 \text{ by at most one in each coordinate}\}.
$$
Equivalently, this is the paper's condition that some exterior lattice
vertex lies at Euclidean distance less than $2$ from $x$.
-/
def LatticeVertexBoundary (S : Set GaussianInt) : Set GaussianInt :=
-- BODY
  {x | x ∈ S ∧ ∃ y : GaussianInt, y ∉ S ∧
    Int.natAbs (x.re - y.re) <= 1 ∧ Int.natAbs (x.im - y.im) <= 1}

end ApollonianSuperharmonic

end
