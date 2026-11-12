/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FiniteTile

-- [TABLET NODE: FordCellDomain]

/-!
# FordCellDomain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The Ford cell domain of denominator $q$ is the half-open $q$-by-$q$ square
of cell basepoints
$$
 D^{\mathrm F}_q=\{x+yi:0\leq x<q,\ 0\leq y<q\}.
$$
This is a set of cells.  It is distinct from the closed vertex domain
$[0,q]^2$ on which the Ford odometer is prescribed.
-/
def FordCellDomain (q : Nat) : FiniteTile :=
-- BODY
  ((Finset.range q).product (Finset.range q)).image
    (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))

end ApollonianSuperharmonic

end
