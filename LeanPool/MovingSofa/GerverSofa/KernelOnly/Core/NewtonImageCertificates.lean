/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle004

/-!
# Newton-center and self-map certificates

These numerical checks use the center cache and preconditioner. They can be
checked while the independent Jacobian and product-cell computations are built.
-/

public section
namespace GerverSofa.PartALeanCert.NewtonImageCertificates

open LeanCert.Core LeanCert.Engine

/-- The center evaluations lie in the intervals supplied to the Newton image. -/
theorem centers_contained : ∀ coordinate : Fin 22,
    intervalContained (pointEvalIntervalsKernel fullExpr (zeroCenter (n := 22)) cfg coordinate)
      (fullPointCache coordinate) := by
  delta intervalContained
  decide +kernel

/-- The cached Newton image is strictly inside the box in each coordinate. -/
theorem images_inside : ∀ coordinate : Fin 22,
    intervalStrictInside (fullImageCachedQ coordinate) (unitBox coordinate) = true := by
  decide +kernel

end GerverSofa.PartALeanCert.NewtonImageCertificates
