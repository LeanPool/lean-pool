/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.QuadraticGrowthAtInfinity

-- [TABLET NODE: IntegerSuperharmonicRepresentative]

/-!
# IntegerSuperharmonicRepresentative

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $A$ be a real $2\times2$ matrix and let
$g:\mathbb Z[i]\to\mathbb Z$.  We call $g$ an integer superharmonic
representative for $A$ when $A$ is symmetric, $g$ has quadratic growth $A$
at infinity in the sense of `QuadraticGrowthAtInfinity`, and
$$
 \Delta g(x)\leq1
$$
for every lattice point $x$, with $\Delta$ as in
`FourNeighborLaplacian`.
-/
def IntegerSuperharmonicRepresentative
    (A : Matrix (Fin 2) (Fin 2) ℝ) (g : IntegerLatticeFunction) : Prop :=
-- BODY
  A.IsSymm ∧ QuadraticGrowthAtInfinity A g ∧
    ∀ x, FourNeighborLaplacian g x ≤ 1

end ApollonianSuperharmonic

end
