/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeHomogenizationJoint
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichlet
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeExponentialMoment

/-!
# ExitTimeHomogenizationJointMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The normalized exponential moment of an exit time

A uniform bound `E_x[τ(U)] ≤ T` for the expected exit time, valid from every
starting point, normalizes a positive exponential moment of the exit time to
`2`: at the multiplier `K = 38` the survival probability at the horizon `K T`
is at most `K⁻¹`, and the rate `λ` is admissible as soon as
`exp (38 λ T) ≤ 19/10`, that is `λ ≤ log(19/10)/(38 T)`.

The uniform bound is only available at the starting points of `U`, whereas the
normalization asks for it at every starting point.  The two agree: a process
started outside `U` leaves it at once, so the expected exit time vanishes
there.

## Main results

* `expectedExitTime_le_of_le_on` — the uniform bound extended from the starting
  points of `U` to every starting point.
* `lintegral_exponentialStoppingWeight_exitTime_le_two_of_le_on` — the
  normalized exponential moment from a bound valid on the open set only.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The normalized exponential moment -/

section Generic

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

omit [LocallyCompactSpace alpha] in
/-- **A bound on the open set bounds the expected exit time everywhere.**  A
process started outside the open set leaves it at once. -/
theorem expectedExitTime_le_of_le_on (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (hKreg : P.KolmogorovRegular hP)
    {U : Set alpha} {c : ℝ≥0∞} (hbound : ∀ z ∈ U, expectedExitTime P hP U z ≤ c)
    (z : alpha) : expectedExitTime P hP U z ≤ c := by
  by_cases hz : z ∈ U
  · exact hbound z hz
  · rw [expectedExitTime_eq_zero_of_notMem P hP hKreg hz]
    exact zero_le

/-- **The normalized exponential moment of the exit time.**  If the expected
exit time from the open set `U` is at most `T` from every point of `U`, then
every rate `λ ≥ 0` with `38 λ T ≤ log(19/10)` has exponential moment at most
`2`, from every starting point. -/
theorem lintegral_exponentialStoppingWeight_exitTime_le_two_of_le_on
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hKreg : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ z ∈ U, expectedExitTime P hP U z ≤ ENNReal.ofReal T)
    {lam : ℝ} (hlam : 0 ≤ lam) (hrate : lam * (38 * T) ≤ Real.log (19 / 10))
    (x : alpha) :
    ∫⁻ eta, ContinuousPath.exponentialStoppingWeight lam
        (ContinuousPath.exitTime U) eta ∂(IsConservative.continuousProcess P hP x) ≤ 2 := by
  have hcoe : ((Real.toNNReal T : NNReal) : ℝ≥0∞) = ENNReal.ofReal T := rfl
  have hreal : ((Real.toNNReal T : NNReal) : ℝ) = T := Real.coe_toNNReal T hT
  have hM : ∀ z : alpha, ∫⁻ eta, ContinuousPath.exitTime U eta
      ∂(IsConservative.continuousProcess P hP z) ≤ ((Real.toNNReal T : NNReal) : ℝ≥0∞) := by
    intro z
    rw [hcoe]
    exact expectedExitTime_le_of_le_on P hP hKreg hbound z
  have hK1 : (1 : ℝ≥0) < 38 := by norm_num
  have hexp : Real.exp (lam * (((38 : ℝ≥0) : ℝ) * ((Real.toNNReal T : NNReal) : ℝ))) ≤
      19 / 10 := by
    have hval : lam * (((38 : ℝ≥0) : ℝ) * ((Real.toNNReal T : NNReal) : ℝ)) =
        lam * (38 * T) := by
      rw [hreal]
      norm_num
    rw [hval]
    calc Real.exp (lam * (38 * T)) ≤ Real.exp (Real.log (19 / 10)) :=
          Real.exp_le_exp.2 hrate
      _ = 19 / 10 := Real.exp_log (by norm_num)
  have h38 : ((38 : ℝ≥0) : ℝ) = 38 := by norm_num
  have hrate' : Real.exp (lam * (((38 : ℝ≥0) : ℝ) * ((Real.toNNReal T : NNReal) : ℝ))) *
      (((38 : ℝ≥0) : ℝ) + 2) ≤ 2 * ((38 : ℝ≥0) : ℝ) := by
    set E : ℝ := Real.exp (lam * (((38 : ℝ≥0) : ℝ) * ((Real.toNNReal T : NNReal) : ℝ)))
      with hE_def
    rw [h38]
    linarith only [hexp]
  exact hP.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le P hFeller hKreg
    U hU (Real.toNNReal T) hM 38 hK1 lam hlam hrate' x

end Generic

end

end Algsuperdiff.Section5.Provider
