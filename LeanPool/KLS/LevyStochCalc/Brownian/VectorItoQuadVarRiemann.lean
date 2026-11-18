/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds
public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition

/-!
# The quadratic-variation Riemann sum for a vector Itô process

Multiplying the increments of two coordinates of a continuous vector Itô process across a uniform
grid and weighting them by a bounded function of the process gives a Riemann sum for
`∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`. Expanding the product of increments leaves five
pieces: the drift–drift term, the two drift–martingale terms, the compensated products on the
diagonal in the Brownian index, the cross terms off that diagonal, and a frozen-weight Riemann
sum for the density `∑ₖ H^{p,k} H^{q,k}`.

## Parts

* `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` — `L¹` bounds for weighted sums of
  cell terms, and the four error terms of the product of increments.
* `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` — the decomposition of the
  weighted product sum into six groups and the `L¹` rate of convergence of the Riemann sum.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` — the `L¹` bound for a weighted
  sum of cell terms with a common first-absolute-moment bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` — the
  drift–drift term.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_driftCross_le` — a
  drift–martingale term.
-/
