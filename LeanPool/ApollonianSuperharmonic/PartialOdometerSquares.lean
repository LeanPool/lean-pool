/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: PartialOdometerSquares]

/-!
# PartialOdometerSquares

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a partial odometer $h$ with domain $T(h)$, let $S(h)$ be the finite set
of all $x\in\mathbb Z[i]$ for which the four vertices
$x,x+1,x+i,x+1+i$ all belong to $T(h)$.  Thus $S(h)$ indexes the unit
squares wholly contained in the domain.
-/
def PartialOdometerSquares (h : PartialOdometer) : Finset GaussianInt :=
-- BODY
  h.domain.filter fun x =>
    x + 1 ∈ h.domain ∧ x + ⟨0, 1⟩ ∈ h.domain ∧
      x + 1 + ⟨0, 1⟩ ∈ h.domain

end ApollonianSuperharmonic

end
