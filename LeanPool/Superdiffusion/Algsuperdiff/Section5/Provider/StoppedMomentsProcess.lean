/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMoments
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ScalarWeakMaximumPrinciple
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicDensity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationWhole

/-!
# StoppedMomentsProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coordinate decomposition of the squared displacement

The stopped second moment of `StoppedMoments.lean` is proved one observable at a time, and the
second moment of the whole displacement is obtained by summing it over the coordinate
directions.  This file records the decomposition that sum rests on: the squared norm is the sum
of the squares of the coordinate observables, both on the state space and, for observables cut
off by a common factor, on its one-point carrier.

## Main results

* `sum_quadraticObservable_basisVec` — the coordinate decomposition of the squared norm.
* `onePointRealExtension_sum_quadraticObservable` — the same on the one-point carrier, for the
  cut-off observables.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The squared norm is the sum of the squares of the coordinate observables. -/
theorem sum_quadraticObservable_basisVec (y : Vec d) :
    ∑ i, quadraticObservable (basisVec i) y = vecNormSq y := by
  simp only [quadraticObservable, vecDot_basisVec_left]
  rfl

/-- The same decomposition for the coordinate observables cut off by a common factor, read on
the one-point carrier. -/
theorem onePointRealExtension_sum_quadraticObservable (c : Vec d → ℝ)
    (z : OnePoint (Vec d)) :
    ∑ i, onePointRealExtension
        (fun y ↦ c y * quadraticObservable (basisVec i) y) z =
      onePointRealExtension (fun y ↦ c y * vecNormSq y) z := by
  induction z using OnePoint.rec with
  | infty => simp only [onePointRealExtension_infty, Finset.sum_const_zero]
  | coe y =>
      simp only [onePointRealExtension_coe, ← Finset.mul_sum, sum_quadraticObservable_basisVec]

end

end Algsuperdiff.Section5.Provider
