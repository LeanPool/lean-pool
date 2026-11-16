/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityTruncation
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityDyadic
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityShifted
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityRectSimple
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityMarkApprox
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityStepIntegral
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityBoxIsometry
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityMarkSum
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityRefinement
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityLimit

/-!
# Density of adapted simple predictable integrands (compensated Poisson)

Toward the L²-completion of the compensated-Poisson simple integral: adapted
`SimplePredictable` integrands are dense in `L²(P ⊗ ds ⊗ ν)`. The construction
reduces a general predictable square-integrable integrand `φ : Ω → ℝ → E → ℝ` to a
bounded one by truncation, then discretizes time and the mark space, and passes to
the limit in `L²(P)`. Compensated mirror of `Brownian/ItoDensity.lean`.

This module collects the development, which is spread over the following parts.

* `CompensatedDensityTruncation`: value and mark truncation of a square-integrable integrand.
* `CompensatedDensityDyadic`: dyadic time-discretisation with the mark carried as a parameter.
* `CompensatedDensityShifted`: the adapted (left-shifted) dyadic eval.
* `CompensatedDensityRectSimple`: rectangle-simple functions and their `L²` density.
* `CompensatedDensityMarkApprox`: mark discretisation of the shifted dyadic eval.
* `CompensatedDensityStepIntegral`: step (finite-sum) predictable integrands.
* `CompensatedDensityBoxIsometry`: weighted covariances of compensated boxes.
* `CompensatedDensityMarkSum`: the mark-sum process and its `L²` isometry.
* `CompensatedDensityRefinement`: Doob `L²` bricks and dyadic cross-resolution refinement.
* `CompensatedDensityLimit`: the cross-resolution Cauchy estimate and the `L²` limit.
-/
