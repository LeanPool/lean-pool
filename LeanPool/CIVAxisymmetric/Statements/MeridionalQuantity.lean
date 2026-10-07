/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient

/-!
# Meridional Quantity

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The integrand of `G_ρ` in `eq:aniso:G`: `|∂_r u_r| + |u_r/r| + |∂_z u_z| + |∂_z u_r|`
on the meridional plane. -/
@[expose] def meridionalQuantity (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  |CKN.spatialPartial (fun w => u w 0) 0 z| + |radialQuotient u z| +
    |CKN.spatialPartial (fun w => u w 2) 2 z| + |CKN.spatialPartial (fun w => u w 0) 2 z|

end CIV
