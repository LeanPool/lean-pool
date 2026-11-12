/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: RealFourNeighborLaplacian]

/-!
# RealFourNeighborLaplacian

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a real-valued function $u:\mathbb Z[i]\to\mathbb R$, define its
four-neighbor Laplacian by
$$
 \Delta_{\mathbb R}u(x)=u(x+1)+u(x-1)+u(x+i)+u(x-i)-4u(x).
$$
-/
def RealFourNeighborLaplacian (f : GaussianInt -> Real)
    (x : GaussianInt) : Real :=
-- BODY
  f (x + 1) + f (x - 1) + f (x + ⟨0, 1⟩) + f (x - ⟨0, 1⟩) - 4 * f x

end ApollonianSuperharmonic

end
