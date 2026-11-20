/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedJump

/-!
# The exterior cross-normalized axial Ponomarenko branch

This file defines the exterior axial branch `axialOutside N κ r = -I₁(κ) K₁(κr) / (iN)`
associated with the cross-normalized transverse branches: the axial component that the
divergence formula of `lem:axial-recovery`, `b₃ = -(iN)⁻¹ div⊥ h`, produces from the decaying
transverse branches, reduced to a cross-normalized order-one product.  It enters the exterior
radial bounds of `Local/PonomarenkoCartesianExteriorDerivative.lean` and
`Local/PonomarenkoExteriorSecondDerivative.lean`.

No radial differential equation, regularity, decay or Sobolev statement is made here.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoCrossNormalizedAxial

open Complex
open PonomarenkoCrossNormalizedJump

/-- The exterior cross-normalized axial branch obtained from the divergence numerator. -/
def axialOutside (N : ℝ) (κ r : ℂ) : ℂ :=
  -(ModifiedBessel.I1 κ * ModifiedBessel.K1 (κ * r)) / (I * (N : ℂ))

end PonomarenkoCrossNormalizedAxial
end FastDynamo
