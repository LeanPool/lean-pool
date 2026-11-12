/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FordVertexDomain

-- [TABLET NODE: FordDoubledBoundary]

/-!
# FordDoubledBoundary

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The doubled boundary of the closed Ford vertex square is
$$
 B_q=[0,q]^2\setminus[2,q-2]^2.
$$
Thus it contains the outer two vertex layers (with the evident convention
when the displayed inner square is empty).
-/
def FordDoubledBoundary (q : Nat) : Set GaussianInt :=
-- BODY
  {x | x ∈ FordVertexDomain q ∧
    ¬(2 <= x.re ∧ x.re <= (q : Int) - 2 ∧
      2 <= x.im ∧ x.im <= (q : Int) - 2)}

end ApollonianSuperharmonic

end
