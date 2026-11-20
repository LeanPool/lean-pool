/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import LeanPool.FastDynamo.Global.WholePlaneW1InfCertificates

/-!
# The constant-coefficient weak resolvent equation

Where the added axial velocity of the selected cell is constant and the local
flow is removed, the background operator of `eq:background-operator` has
constant coefficients, and its resolvent equation is, componentwise, the
scalar equation

`(-epsilon * Δ + mu) g = f`.

This file defines the weak form of that equation on the whole plane, with
`L²` forcing, as the predicate `IsConstantCoefficientWeakResolventSolution`; it
stores the equation and no estimate.  `WholePlaneEllipticRegularity`
proves that a weak solution has an `L²` Laplacian, and
`Local/HorizontalFormStrongIdentification.lean` applies this to the local seed problem.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace ConstantCoefficientBackground

/-! ## Forced weak equation -/

/-- A weak solution of the constant-coefficient resolvent equation
with `L²` forcing.  This stores the equation, not any estimate. -/
def IsConstantCoefficientWeakResolventSolution
    (epsilon : ℝ) (mu : ℂ) (f : WholePlaneScalarL2)
    (g : WholePlaneScalarH1) : Prop :=
  ∀ phi : WholePlaneScalarH1,
    constantCoefficientWeakForm epsilon mu g phi =
      inner ℂ (wholePlaneH1Embedding ℂ phi) f

end ConstantCoefficientBackground

end

end FastDynamo
