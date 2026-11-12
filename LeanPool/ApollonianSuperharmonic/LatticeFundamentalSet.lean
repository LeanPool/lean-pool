/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: LatticeFundamentalSet]

/-!
# LatticeFundamentalSet

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a sublattice $L\subseteq\mathbb Z[i]$, a finite set $R$ is a complete
set of coset representatives if every $x\in\mathbb Z[i]$ has a unique
$r\in R$ with $x-r\in L$.
-/
def LatticeFundamentalSet (L : AddSubgroup GaussianInt)
    (R : Finset GaussianInt) : Prop :=
-- BODY
  ∀ x : GaussianInt, ∃! r : GaussianInt, r ∈ R ∧ x - r ∈ L

end ApollonianSuperharmonic

end
