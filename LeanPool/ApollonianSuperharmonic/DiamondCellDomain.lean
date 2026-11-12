/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FiniteTile

-- [TABLET NODE: DiamondCellDomain]

/-!
# DiamondCellDomain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The diamond cell domain of parameter $k$ is the $2k$-row staircase
polyomino
$$
 D^{\mathrm D}_k=
 \bigcup_{0\leq y<2k}
 \{x+yi:-r_y\leq x<r_y\},\qquad
 r_y=\min(y+1,2k-y).
$$
Its row lengths are $2,4,\ldots,2k,2k,\ldots,4,2$.  This cell domain is
not either odometer vertex set $T_k$ or $T'_k$.
-/
def DiamondCellDomain (k : Nat) : FiniteTile :=
-- BODY
  (Finset.range (2 * k)).biUnion fun y =>
    let r := Nat.min (y + 1) (2 * k - y)
    (Finset.range (2 * r)).image fun j =>
      (⟨((j : Nat) : Int) - (r : Int), (y : Int)⟩ : GaussianInt)

end ApollonianSuperharmonic

end
