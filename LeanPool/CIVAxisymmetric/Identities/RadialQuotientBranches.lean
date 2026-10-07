/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.RadialQuotient

/-!
# Radial Quotient Branches

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN
open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- When `z` is off the axis (`z.1 0 ≠ 0`), the radial quotient reduces to `u z 0 / z.1 0`. -/
theorem radialQuotient_off_axis (u : ParabolicPoint → Vec3) {z : ParabolicPoint} (hz : z.1 0 ≠ 0) :
    radialQuotient u z = u z 0 / z.1 0 := by
  simp only [radialQuotient]
  rw [ite_eq_right hz]

/-- When `z` lies on the axis (`z.1 0 = 0`), the radial quotient is the spatial partial of
`u(·, 0)` at `0` in direction `z.1`, i.e. `∂₁(u(·, 0))(0)`. -/
theorem radialQuotient_on_axis (u : ParabolicPoint → Vec3) {z : ParabolicPoint} (hz : z.1 0 = 0) :
    radialQuotient u z = CKN.spatialPartial (fun w => u w 0) 0 z := by
  simp only [radialQuotient]
  rw [ite_eq_left hz]

end CIV
