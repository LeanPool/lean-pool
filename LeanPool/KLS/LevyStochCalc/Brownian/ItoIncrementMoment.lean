/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMomentRestrict
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMomentBounds

/-!
# Moments of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian. The bound is the
per-tile variance budget of `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to
simple approximants of `1_{(a, b]}·H` that themselves vanish off `(a, b]`, obtained by
multiplying an approximant by `stepIoc` on their common refinement. The second and third
absolute moments are bounded from the same construction.

The development is split into:

* `LevyStochCalc.Brownian.ItoIncrementMomentRestrict` — restriction of an adapted simple
  integrand to `(a, b]` and the variance budget of the resulting per-tile bound.
* `LevyStochCalc.Brownian.ItoIncrementMomentBounds` — the fourth-, second- and third-moment
  bounds for an increment of the `L²` Itô integral.
-/
