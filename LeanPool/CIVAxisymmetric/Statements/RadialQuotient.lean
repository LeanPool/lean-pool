/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Radial Quotient

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The quotient `u_r / r` read on the meridional plane: `u₁ / x₁` off the axis and `∂₁ u₁` on
it. For a field that is smooth and axisymmetric, `u₁` vanishes on the axis, so the axis value is
the limit of `u₁ / x₁`: this is the manuscript's "`u_r/r` extended continuously across the axis"
(paragraph after `eq:aniso:G`; design note R7). -/
@[expose] def radialQuotient (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  if z.1 0 = 0 then CKN.spatialPartial (fun w => u w 0) 0 z else u z 0 / z.1 0

end CIV
