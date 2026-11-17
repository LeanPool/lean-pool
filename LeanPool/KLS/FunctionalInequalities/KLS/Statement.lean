/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.Poincare.LocalSlope.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The KLS conjecture as a Lean proposition

Source: Blueprint `conj:kls`, in its covariance-normalized literature formulation.
One finite nonnegative constant is chosen before every dimension and every probability law.
The target includes dimension zero, singular affine supports, and a finite second moment.
It uses the literature local-slope constant, not an arbitrary supplied energy.

This file defines a proposition. It contains no proof of KLS and no assertion of equivalence
with the isotropic formulation. The affine/isotropic equivalence is proved separately in
`KLS/LogConcave/Isotropic.lean`, and the selected/literature bridge in
`KLS/LogConcave/Poincare.lean`; neither supplies a dimension-free bound. This declaration is
versioned with its definitions, not API-frozen.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS

/-- One finite nonnegative constant bounds the intrinsic local-slope Poincaré constant by
`C * ‖Covariance.operator μ‖` for every dimension and every log-concave probability law with
finite second moment. The covariance is centered. Dimension zero and singular affine supports
are included; no isotropic normalization is imposed on the input law. -/
def Conjecture : Prop :=
  ∃ C : NNReal, ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
    LogConcave μ → MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
      Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤ (C : ENNReal) *
        ENNReal.ofReal ‖Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))‖

end FunctionalInequalities.KLS
