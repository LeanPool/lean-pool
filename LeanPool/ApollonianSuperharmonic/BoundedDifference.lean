/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: BoundedDifference]

/-!
# BoundedDifference

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two integer lattice functions $f$ and $g$ have bounded difference if there
is a natural number $B$ such that $|f(x)-g(x)|\leq B$ for every
$x\in\mathbb Z[i]$.
-/
def BoundedDifference (f g : IntegerLatticeFunction) : Prop :=
-- BODY
  ∃ B : ℕ, ∀ x, Int.natAbs (f x - g x) ≤ B

end ApollonianSuperharmonic

end
