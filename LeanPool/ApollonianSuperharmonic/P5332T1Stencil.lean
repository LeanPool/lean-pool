/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordFareyParameter

-- [TABLET NODE: P5332T1Stencil]

/-!
# P5332T1Stencil

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A Ford contact stencil is a record consisting of an integral displacement
$d$, an integral affine coefficient $a$, a contact center $z$, an integral
companion displacement $w$, and five integer values $V_0,\ldots,V_4$.
The value order is always $z,z+1,z-1,z+i,z-i$.  The companion displacement
is used for child--parent contacts; it is set to zero for equal-square
contacts.
-/
structure P5332T1Stencil where
-- BODY
  /-- The spatial translation in the contact identity. -/
  displacement : GaussianInt
  /-- The Gaussian coefficient of the affine correction. -/
  linear : GaussianInt
  /-- The lattice vertex at the center of the five-point contact stencil. -/
  center : GaussianInt
  /-- The companion displacement, zero for equal-square contacts. -/
  companion : GaussianInt
  /-- The prescribed values at the center, east, west, north and south vertices. -/
  values : Fin 5 → Int

end ApollonianSuperharmonic

end
