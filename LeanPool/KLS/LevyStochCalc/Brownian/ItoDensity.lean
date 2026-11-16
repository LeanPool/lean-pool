/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityDyadicAverages
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityShiftedAverages
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityPointwise
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityPredictableL2
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityUnbounded

/-!
# Density of simple predictable processes in L²

Dyadic approximation of `L²(Ω × [0,T])` integrands by simple predictable
processes, giving the density results `simplePredictable_dense_L2` and
`adaptedSimple_dense_L2_brownian` that extend the Itô integral off the simple
class. Builds on `Brownian/ItoSimple.lean`.

The development is split into
`Brownian/ItoDensityDyadicAverages.lean` (truncation and the dyadic cell averages),
`Brownian/ItoDensityShiftedAverages.lean` (left-shifted averages and cell-average identities),
`Brownian/ItoDensityPointwise.lean` (almost-everywhere convergence of the averages),
`Brownian/ItoDensityPredictableL2.lean` (`L²` convergence in the bounded case) and
`Brownian/ItoDensityUnbounded.lean` (the density results in general).
-/
