/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordCellDomain
public import Mathlib.Data.Int.Interval

-- [TABLET NODE: P4062T1InteriorSquare]

/-!
# P4062T1InteriorSquare

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an integer denominator $q\geq0$, let $D_q$ be the finite set of lattice
vertices $(a,b)$ with $1\leq a,b\leq q-1$.
-/
def P4062T1InteriorSquare (q : Nat) : Finset GaussianInt :=
-- BODY
  ((Finset.Icc (1 : Int) ((q : Int) - 1)).product
    (Finset.Icc (1 : Int) ((q : Int) - 1))).image
      (fun a => (⟨a.1, a.2⟩ : GaussianInt))

end ApollonianSuperharmonic

end
