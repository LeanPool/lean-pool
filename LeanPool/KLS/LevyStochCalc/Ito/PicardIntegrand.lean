/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardIntegrandBounds
public import LeanPool.KLS.LevyStochCalc.Ito.PicardIntegrandFrozen

/-!
# The Picard step's hypotheses along a frozen process

`picardStep` asks for its integrands to be square integrable at **every** horizon, while a
member of the process space is `L²`-controlled only on `[0, T]`. Running the step on the frozen
process `X.stop` closes that gap: off `[0, T]` the frozen path repeats `X_T`, so the linear
growth supplied by `IsLipschitz` turns `IsRegular`'s bounds at a single state into bounds along
the path at every horizon.

## Parts

* `LevyStochCalc.Ito.PicardIntegrandBounds` — linear growth of the coefficients, square
  integrability of the drift, diffusion and jump integrands along a state process of finite
  horizon energy, and measurability of a coefficient composed with a state process.
* `LevyStochCalc.Ito.PicardIntegrandFrozen` — the same properties for a path frozen at the
  horizon, and the Picard step run on a frozen member of the process space or on a frozen raw
  state process.

## Main statements

* `LevyStochCalc.Ito.Picard.sq_norm_le_sum_sq` — the supremum norm on `Fin n → ℝ` is dominated
  by the Euclidean sum of squares.
* `LevyStochCalc.Ito.Picard.sq_sigma_le` — linear growth of `σ` in the state.
* `LevyStochCalc.Ito.Picard.lintegral_sq_sigma_stop_lt_top`,
  `LevyStochCalc.Ito.Picard.lintegral_sq_gamma_stop_lt_top` — the diffusion and jump integrands
  along the frozen process are square integrable at every horizon.
* `LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state`,
  `LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state` — composing a jointly
  measurable coefficient with a progressively measurable state process.
-/
