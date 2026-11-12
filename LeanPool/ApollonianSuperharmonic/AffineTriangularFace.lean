/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble

-- [TABLET NODE: AffineTriangularFace]

/-!
# AffineTriangularFace

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
An affine triangular face is a tagged lattice point: for each
$z\in\mathbb Z^2$ there is an upward face $U_z$ and a downward face $D_z$.
The tags distinguish the two face orbits even when their base points differ.
-/
inductive AffineTriangularFace : Type where
-- BODY
  | up (base : Int × Int)
  | down (base : Int × Int)
  deriving DecidableEq

end ApollonianSuperharmonic

end
