/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: FourNeighborLaplacian]

/-!
# FourNeighborLaplacian

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an integer lattice function $f$ and $x\in\mathbb Z[i]$, its
four-neighbor discrete Laplacian is
$$
 \Delta f(x)=f(x+1)+f(x-1)+f(x+i)+f(x-i)-4f(x)
              =\sum_{y\sim x}(f(y)-f(x)).
$$
-/
def FourNeighborLaplacian (f : IntegerLatticeFunction)
    (x : GaussianInt) : ℤ :=
-- BODY
  f (x + 1) + f (x - 1) + f (x + ⟨0, 1⟩) + f (x - ⟨0, 1⟩) - 4 * f x

end ApollonianSuperharmonic

end
