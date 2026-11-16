/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardBieleckiNorm
public import LeanPool.KLS.LevyStochCalc.Ito.PicardStepMap
public import LeanPool.KLS.LevyStochCalc.Ito.PicardStochasticLipschitz

/-!
# Picard iteration operator for jump-diffusion SDEs

The Picard iteration scheme used to construct strong solutions of the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t⁻}, e) Ñ(dt, de)`,

following Applebaum (2009, Thm 6.2.9) / Ikeda–Watanabe (Ch. IV): Picard iteration in the space
`S²([0,T]; ℝⁿ)` of L²-sup-bounded adapted processes, with the contraction provided by a
Bielecki-weighted norm `‖X‖_β := sup_{t ≤ T} e^{-βt} √(𝔼‖X_t‖²)`.  This module is the union of
its parts:

* `Ito/PicardBieleckiNorm.lean` — `bieleckiNorm`, the process space `SBoundedProcess` with its
  deterministic-time freeze `SBoundedProcess.stop`, the drift component `picardStep_drift` of the
  Picard map and the per-component Lipschitz estimates of that component.
* `Ito/PicardStepMap.lean` — the vector and integrated drift estimates, the Bielecki
  exponential-weight calculus, and the Picard map `picardStep` with its components
  `picardStep_diffusion` and `picardStep_jump`.
* `Ito/PicardStochasticLipschitz.lean` — `itoIsometry_diff_brownian` and the per-component
  `L²`-Lipschitz estimates `picardStep_diffusion_diff_lipschitz_sq_componentwise` and
  `picardStep_jump_diff_lipschitz_sq_componentwise`.

The complete-metric-space structure on the process space lives in `PicardSpace.lean`; the Banach
fixed-point conclusion in `PicardFixedPoint.lean`.
-/
