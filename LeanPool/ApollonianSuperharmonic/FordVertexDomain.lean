/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: FordVertexDomain]

/-!
# FordVertexDomain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The closed Ford vertex domain of denominator $q$ is
$$
 V_q^{\mathrm F}=[0,q]^2\cap\mathbb Z^2.
$$
It is a vertex set and is distinct from the half-open cell-basepoint set
`FordCellDomain`.
-/
def FordVertexDomain (q : Nat) : Set GaussianInt :=
-- BODY
  {x | 0 <= x.re ∧ x.re <= (q : Int) ∧ 0 <= x.im ∧ x.im <= (q : Int)}

end ApollonianSuperharmonic

end
