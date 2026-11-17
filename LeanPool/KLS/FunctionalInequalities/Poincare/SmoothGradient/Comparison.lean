/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothGradient.Intrinsic
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothGradient.Ambient

/-!
# Ambient and intrinsic-affine Poincaré comparisons

Proved optimizer consequences for `lem:ambient-intrinsic-poincare-comparison`.
The two functionals are represented on the same original `L²(μ)` space, so the variance is
identical and energy equality identifies both their finite domains and their optimal constants.

Source: Blueprint `cor:ambient-intrinsic-constant-equality` and its energy-level predecessor.
Neither raw/core agreement nor a literature or Cheeger-energy identification is a premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.SmoothGradient.Ambient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/-- Ambient and intrinsic-affine inequalities have the same valid finite constants.
Source: exact equality of the relaxed energies on their common ambient carrier. -/
theorem holds_iff_intrinsic (C : NNReal) :
    Holds μ C ↔ Poincare.SmoothGradient.Intrinsic.Holds μ C := by
  unfold Holds Poincare.SmoothGradient.Intrinsic.Holds
  rw [Energy.SmoothGradient.relaxation_eq_intrinsic_energy]

/-- The ambient and selected optima agree in `ENNReal`, with no finiteness assumption.
Source: Blueprint `cor:ambient-intrinsic-constant-equality`. -/
theorem constant_eq_intrinsic :
    optimalConstant μ = Poincare.SmoothGradient.Intrinsic.optimalConstant μ := by
  unfold optimalConstant Poincare.SmoothGradient.Intrinsic.optimalConstant
  rw [Energy.SmoothGradient.relaxation_eq_intrinsic_energy]

end FunctionalInequalities.Poincare.SmoothGradient.Ambient
