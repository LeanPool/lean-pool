/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Trajectory.ExitTimeSurvival

/-!
# SurvivalProbability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Survival of the exit time from a cube at a fixed fraction of the time scale

Two moment bounds at a common time scale `T` produce a lower bound on the probability that the
diffusion stays in an open set `U` for a time comparable to `T`: an upper bound
`E_y tau_U ≤ Cup * T` valid from every starting point, and a lower bound `clow * T ≤ E_x tau_U`
at the starting point under consideration.  The upper bound controls the second moment, and the
Paley--Zygmund inequality at the level one half then gives

  `clow ^ 2 / (1152 * Cup ^ 2) ≤ Q_x {clow * T / 2 ≤ tau_U}`.

The bound is uniform over any set of starting points at which the lower bound holds, which is the
form in which the survival probability is used: the level `clow * T / 2` and the probability
`clow ^ 2 / (1152 * Cup ^ 2)` depend only on the two moment constants, not on the starting point
and not on the scale `T`.

Both moment bounds are hypotheses here.  The time scale is required to be positive because at
`T = 0` the level `clow * T / 2` is zero, so the event is all of path space and, the kernel being
a probability measure, has probability one; the conclusion would then read
`clow ^ 2 ≤ 1152 * Cup ^ 2`, which is false for `clow > 34 * Cup`.  Both moment bounds do hold at
`T = 0`, for instance for `U = ∅`, where the exit time vanishes identically.
-/

open HCPolySupport MeasureTheory Set
open scoped ENNReal NNReal

namespace Algsuperdiff.Section5.Trace

noncomputable section

/-- The survival probability delivered by the two expected-exit-time bounds: the Paley--Zygmund
constant `(1 - rho) ^ 2 * clow ^ 2 / (288 * Cup ^ 2)` at the level `rho = 1 / 2`. -/
def survivalProbabilityConstant (Cup clow : ℝ≥0) : ℝ≥0 := clow ^ 2 / (1152 * Cup ^ 2)

end

end Algsuperdiff.Section5.Trace
