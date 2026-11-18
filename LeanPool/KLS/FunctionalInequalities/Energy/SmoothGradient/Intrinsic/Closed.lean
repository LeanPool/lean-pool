/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Closed

/-!
# Closed quadratic energy in intrinsic affine coordinates

The intrinsic-coordinate map identifies the original real `L²` space linearly and isometrically
with real `L²` of the probability law on the direction of its affine support. Pulling the
closed smooth-gradient relaxation back along this equivalence preserves the complete
closed-quadratic structure.

This is an intrinsic-affine smooth-relaxation theorem. It is not an identification with Cheeger
energy, a Markov theorem, or an agreement statement for raw ambient gradients.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Energy.SmoothGradient.Intrinsic

open Energy.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The intrinsic-affine smooth-gradient relaxation is a densely defined closed quadratic
functional on the original real `L²(μ)` space. -/
theorem closedQuadratic
    (μ : ProbabilityMeasure E) :
    ClosedQuadratic (energy μ) :=
  (Energy.SmoothGradient.relaxation_closedQuadratic
    (Probability.intrinsicMeasure μ)).comap_linearIsometryEquiv (intrinsicL2Equiv μ)

end FunctionalInequalities.Energy.SmoothGradient.Intrinsic
