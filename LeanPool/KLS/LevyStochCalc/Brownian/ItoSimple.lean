/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimpleIntegrand
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimpleMoments
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimpleIsometry

/-!
# Brownian Itô integral on simple predictable integrands

The simple predictable integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` for a scalar
Brownian motion `W`, their integral `simpleIntegral`, and the L²-isometry on
this class (`simpleIntegral_isometry`, `simpleIntegral_L2_isometry_brownian`).
L²-density of simple predictables is in `Brownian/ItoDensity.lean`; the
martingale property in `Brownian/ItoMartingale.lean`.

The material is divided into `Brownian/ItoSimpleIntegrand.lean` (the integrand class, the
elementary integral and the energy of the integrand), `Brownian/ItoSimpleMoments.lean` (the
second moments of the terms of that integral) and `Brownian/ItoSimpleIsometry.lean` (the
isometry itself).
-/
