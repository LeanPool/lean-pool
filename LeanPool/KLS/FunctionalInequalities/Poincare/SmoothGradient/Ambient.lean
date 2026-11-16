/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Poincare.L2.Energy

/-!
# Poincaré optimization for the smooth-gradient relaxation

This module attaches the generic `L²` Poincaré optimizer to the concrete sequential relaxation
of globally smooth finite-gradient tests. Its names retain `Energy.SmoothGradient.relaxation`: no
unproved identification with Cheeger energy or a closed Sobolev form is hidden here.
-/

@[expose] public section

-- `Ambient` refers to relaxation before passing to affine-support coordinates.

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.SmoothGradient.Ambient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- The optimal Poincaré constant of the smooth-gradient sequential relaxation. -/
def optimalConstant (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] : ENNReal :=
  L2Energy.optimalConstant μ (Energy.SmoothGradient.relaxation μ)

/-- Validity of a finite Poincaré constant on the finite domain of the smooth-gradient
sequential relaxation. -/
def Holds (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] (C : NNReal) : Prop :=
  L2Energy.Holds μ (Energy.SmoothGradient.relaxation μ) C

/-- A finite constant is valid for the smooth-gradient relaxation exactly when it bounds its
optimal extended constant. -/
theorem holds_iff_constant_le (μ : ProbabilityMeasure E)
    [FiniteDimensional ℝ E] [BorelSpace E] [SecondCountableTopology E] (C : NNReal) :
    Holds μ C ↔
      optimalConstant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ (Energy.SmoothGradient.relaxation μ) C

end FunctionalInequalities.Poincare.SmoothGradient.Ambient
