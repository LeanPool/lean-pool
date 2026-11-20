/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoOriginProfiles
public import LeanPool.FastDynamo.Local.PonomarenkoGaussianFactors

/-!
# The complex radius

This module defines `complexRadius y = (‖y‖ : ℂ)`, the physical radius of a point of the
plane embedded into the complex scalar field.  It is the radius in which the exterior
modified-Bessel branches of the Ponomarenko mode are evaluated, by
`Local/PonomarenkoCartesianExteriorDerivative.lean`, `Local/HorizontalModeBranches.lean` and
the other `HorizontalMode*` modules.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace ComplexRadius

open Complex Set Metric
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open PonomarenkoOriginProfiles
open CartesianRadialRegularity

/-- The physical radius embedded into the complex scalar field. -/
def complexRadius (y : WholePlane) : ℂ :=
  (‖y‖ : ℂ)

end ComplexRadius
end FastDynamo
