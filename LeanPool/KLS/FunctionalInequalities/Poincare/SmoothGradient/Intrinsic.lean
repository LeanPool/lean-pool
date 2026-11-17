/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-!
# Poincaré optimization in intrinsic affine coordinates

This module attaches the generic real-`L²` Poincaré optimizer to the closed quadratic
smooth-gradient relaxation on the direction of the affine support. The variance is still the
intrinsic `L²(μ)` variance of the original probability law; only the energy is evaluated through
the linearly isometric intrinsic-coordinate presentation.

The `Poincare.SmoothGradient.Intrinsic` namespace names the frontend selected by the repository: the
intrinsic-affine smooth-gradient relaxation. Its construction remains explicit in
`Energy.SmoothGradient.Intrinsic.energy`; the name itself asserts no Cheeger or spectral
identification.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.SmoothGradient.Intrinsic

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The optimal Poincaré constant of the intrinsic-affine smooth-gradient relaxation. -/
def optimalConstant (μ : ProbabilityMeasure E) : ENNReal :=
  L2Energy.optimalConstant μ
    (Energy.SmoothGradient.Intrinsic.energy μ)

/-- Validity of a finite Poincaré constant on the finite domain of the intrinsic-affine
smooth-gradient relaxation. -/
def Holds
    (μ : ProbabilityMeasure E) (C : NNReal) : Prop :=
  L2Energy.Holds μ (Energy.SmoothGradient.Intrinsic.energy μ) C

omit [CompleteSpace E] in
/-- A finite constant is valid for the intrinsic-affine relaxation exactly when it bounds the
optimal extended constant. -/
theorem holds_iff_constant_le
    (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds μ C ↔
      optimalConstant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ
    (Energy.SmoothGradient.Intrinsic.energy μ) C

end FunctionalInequalities.Poincare.SmoothGradient.Intrinsic
