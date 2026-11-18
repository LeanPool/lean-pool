/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebraProduct
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebraAssociativity

/-!
# Simple integrands inside the `L²` Brownian Itô integral

The `L²` Itô integral is built as a limit of elementary integrals of simple integrands, so a
simple integrand can be fed to it in its own right. This file records that a simple integrand is
progressively measurable and square-integrable on every window, and that the `L²` integral of a
simple integrand is its elementary integral.

## Main statements

* `SimplePredictable.progressivelyMeasurable_eval` — a simple integrand with adapted
  coefficients is progressively measurable.
* `simpleIntegral_diff_isometry_of_adapted` — the difference isometry for two adapted simple
  integrands at an intermediate time, with no constraint relating their horizons.
* `stochasticIntegralBrownian_eval_simple` — the `L²` Itô integral of a simple integrand agrees
  almost everywhere with its elementary integral.
* `SimplePredictable.mulOnCommonRefinement` — the product of two simple integrands, carried on their
  common refinement, together with its evaluation and its adaptedness.
* `SimplePredictable.integralAgainst` — the elementary integral of a simple integrand against an
  arbitrary process.
* `SimplePredictable.sum_xi_mul_simpleIntegral_sub` — the elementary integral of `G` against the
  elementary integral of `K` is the elementary integral of the product `G · K`.
* `isometry_simple_sub_stochasticIntegralBrownian` — the difference isometry between an
  elementary integral and an `L²` integral.
* `stochasticIntegralBrownian_integralAgainst` — summing the increments of the `L²` Itô integral
  of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
  product `G · H`.
* `stepIoc`, `stepIoc₀` — the simple integrand `1_{(a, b]}`.
* `stochasticIntegralBrownian_indicator_Ioc` — restricting the integrand to `(a, b]` gives the
  increment of the integral across `(a, b]`.

## Parts

* `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand` — boundedness, measurability and
  square-integrability of a simple integrand, and the identification of its `L²` Itô integral
  with its elementary integral.
* `LevyStochCalc.Brownian.ItoAlgebraProduct` — the product of two simple integrands on their
  common refinement, the elementary integral against a process, and the isometry comparing an
  elementary integral with an `L²` Itô integral.
* `LevyStochCalc.Brownian.ItoAlgebraAssociativity` — associativity of the `L²` Itô integral
  against a simple integrand, the step integrands `1_{(a, b]}`, and locality.
-/
