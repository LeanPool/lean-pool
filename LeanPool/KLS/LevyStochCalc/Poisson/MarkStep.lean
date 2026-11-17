/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStepIsometry
public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStepWeight
public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStepIncrement

/-!
# Mark-step integrands and their compensated integrals

A *mark-step integrand* is a finite sum `∑ᵢ 𝟙_{(pᵢ, pᵢ₊₁]}(s) ∑ₖ ξᵢₖ(ω) 𝟙_{Bₖ}(e)` over a
time grid `0 = p₀ < ⋯ < p_{N₀}` and finitely many mark sets `Bₖ` of finite `ν`-measure, with
bounded coefficients `ξᵢₖ`. Its compensated integral up to time `t` is
`∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ ∧ t, pᵢ₊₁ ∧ t] × Bₖ)`.

The grid is a separate object (`TimeGrid`) so that integrands on a common grid can be
added; a grid can be clamped at a time `t` (`TimeGrid.clamp`), which expresses the
integral up to `t` as the integral over the whole clamped horizon and thereby gives the
`L²` isometry at every time from the horizon isometry.

The material is split over three files:

* `LevyStochCalc.Poisson.MarkStepIsometry` — `TimeGrid`, `MarkStep`, the compensated
  integral, clamping and the `L²` isometry at every time;
* `LevyStochCalc.Poisson.MarkStepWeight` — sums, negations and weightings of mark-step
  integrands;
* `LevyStochCalc.Poisson.MarkStepIncrement` — dyadic grids, refinement and restriction, and
  weighted increments.
-/
