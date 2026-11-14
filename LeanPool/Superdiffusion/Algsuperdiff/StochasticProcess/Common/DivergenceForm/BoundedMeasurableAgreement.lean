/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableResolvent
public import LeanPool.MarkovProcess.MarkovProcess.Feller.Resolvent
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0Resolvent
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointExtension
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain

/-!
# BoundedMeasurableAgreement

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
The base case of the comparison between the process resolvent on the one-point
carrier and the analytic resolvent on bounded measurable data.
-/

/-!
# The process resolvent and the analytic resolvent agree on `C₀` data

The conservative model semigroup lives on `OnePoint U`, with observables
extended by `0` at the point at infinity.  For an observable coming from
`C₀(U, ℝ)`, its real kernel resolvent at a point of `U` is the value of the
`C₀` representative of the analytic resolvent, hence the value of the
representative continuous on `U` of the analytic resolvent applied to the same
datum read as a bounded measurable function.

This is the base case of the comparison on bounded measurable observables.
The extension from `C₀` data to all bounded measurable data by a monotone
class argument is not carried out here.

Both statements use the coefficient only through the interior regularity
witness `HasContinuousShiftedResolvents`, so they are stated in that form under
the suffix `_reg`; the small-contrast statements keep their names and are
corollaries.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open MarkovProcess MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The zero extension vanishes outside the domain. -/
theorem domainExtension_of_notMem {f : U → ℝ} {x : Vec d} (hx : x ∉ U) :
    domainExtension f x = 0 := by
  have hnot : ¬ ∃ y : U, (y : Vec d) = x := by
    rintro ⟨y, rfl⟩
    exact hx y.2
  simpa [domainExtension] using Function.extend_apply' f (0 : Vec d → ℝ) x hnot

end

end DivergenceFormProcess.Form
