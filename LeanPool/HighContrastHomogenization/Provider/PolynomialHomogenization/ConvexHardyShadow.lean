/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexWhitneyGeometry

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyShadow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Shadows of convex-domain ball chains

A ball in the straight chain from a point to the center of a concentric ball
sandwich casts a controlled Euclidean shadow at the original point.  The
ambient distance between the two chain centers is measured in the supremum
norm; comparison with the Euclidean norm accounts for the factor `sqrt d` in
the shadow radius.

For a maximal Whitney row, every cube whose chain ball contains a fixed point
therefore meets one common Euclidean ball.  The local row-mass estimate then
controls the total volume of all such cubes.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The scale-free coefficient in the volume bound for a straight-chain
shadow of one maximal Whitney row. -/
@[expose]
def convexHardyShadowRowConstant (d : ℕ) (rho Rad L : ℝ) : ℝ :=
  24 * (d : ℝ) * Real.sqrt d * ((rho + Rad) / rho) * (4 : ℝ) ^ d *
    (2 * (L + Real.sqrt d * (Rad / rho))) ^ (d - 1)

end

end HighContrast
end HCPolySupport
