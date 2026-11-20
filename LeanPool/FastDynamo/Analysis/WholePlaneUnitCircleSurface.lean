/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The unit-circle surface term on the whole plane

This file defines the value of the unit-circle surface term on a whole-plane Schwartz test
function, `unitCircleSurfaceValue`: the integral of the test function against a density on the
unit circle, for densities with values in any complex normed space.

Only the surface term itself is defined here.  In particular, no Gauss--Green,
distributional Laplacian, or form-domain interpretation is asserted.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped SchwartzMap

/-- The value of the unit-circle surface term with `F`-valued density `density` on a Schwartz
test function `φ`.  It is generic in the fibre `F`; the horizontal seed chain reads it at
`F = ℂ²`. -/
def unitCircleSurfaceValue {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace ℂ F]
    (density : WholePlaneUnitCircle → F)
    (φ : SchwartzMap WholePlane ℂ) : F :=
  ∫ y : WholePlaneUnitCircle, φ y.1 • density y ∂wholePlaneUnitCircleMeasure

end
end FastDynamo
