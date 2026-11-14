/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: AcyclicIndegreeOrientation]

/-!
# AcyclicIndegreeOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $D$ be a finite set of lattice vertices and let
$\sigma:\mathbb Z[i]\to\mathbb Z$ be an ambient lattice function.  An
\emph{acyclic indegree orientation with data $\sigma$} chooses exactly one
direction on every four-neighbor edge of the induced graph on $D$, chooses
no other directed edges, and has indegree $\sigma(x)$ at each $x\in D$.
Thus only the restriction of the ambient function $\sigma$ to $D$ supplies
the prescribed indegrees.  A natural-valued rank strictly increasing along
every directed edge is included as an explicit certificate of acyclicity.
-/
structure AcyclicIndegreeOrientation (D : Finset GaussianInt)
    (σ : GaussianInt → ℤ) where
-- BODY
  /-- The chosen direction of each edge of the finite lattice graph. -/
  edge : GaussianInt → GaussianInt → Prop
  /-- Decidable membership in the chosen directed edge relation. -/
  edgeDecidable : ∀ x y, Decidable (edge x y)
  /-- A natural rank that increases strictly along each directed edge. -/
  rank : GaussianInt → ℕ
  supported : ∀ x y, edge x y →
    x ∈ D ∧ y ∈ D ∧ FourNeighborAdjacent x y
  oriented : ∀ x ∈ D, ∀ y ∈ D, FourNeighborAdjacent x y →
    (edge x y ∧ ¬ edge y x) ∨ (edge y x ∧ ¬ edge x y)
  increasing : ∀ x y, edge x y → rank x < rank y
  indegree : ∀ x ∈ D,
    ((D.filter fun y => @decide (edge y x) (edgeDecidable y x)).card : ℤ) = σ x

end ApollonianSuperharmonic

end
