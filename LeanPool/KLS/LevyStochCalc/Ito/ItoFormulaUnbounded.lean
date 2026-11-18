/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnboundedClamp
public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands
public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnboundedLimit

/-!
# Itô's formula without a pointwise bound on the coefficients

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients driving
a process that converges to the original one in `L²`, uniformly on a bounded window. The
development is spread over three files, which this one collects:

* `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` — the clamped coefficients and the `L²`
  approximation of the process they drive;
* `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` — convergence of the drift, quadratic
  variation and diffusion integrands built from the clamped coefficients;
* `LevyStochCalc.Ito.ItoFormulaUnboundedLimit` — the limit of the stochastic integrals and Itô's
  formula for unbounded coefficients.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff` — Itô's formula with unbounded
  coefficients, for a function with bounded first and second derivatives.
* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded` — Itô's formula for a `C²` function of a
  vector Itô process, with no bound on either the coefficients or the derivatives.
-/
