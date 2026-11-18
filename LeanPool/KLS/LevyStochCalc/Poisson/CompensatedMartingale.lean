/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedMartingaleAdapted
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedMartingaleIncrement
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedMartingaleQuadratic

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is a martingale for a Poisson filtration of `N`, and its compensated
square `t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` is a martingale as well.
The development is split over three modules:

* `LevyStochCalc.Poisson.CompensatedMartingaleAdapted` — adaptedness, per-term integrability
  and the conditional-expectation identity giving the martingale property of `simpleIntegral`;
* `LevyStochCalc.Poisson.CompensatedMartingaleIncrement` — the clamped compensator in explicit
  form, the increment decomposition over the increment boxes, and the box-level moment
  identities (past-independence, diagonal second moment, off-diagonal vanishing);
* `LevyStochCalc.Poisson.CompensatedMartingaleQuadratic` — the set-level weighted
  quadratic-variation isometry, `L²`-membership, and the compensated-square martingale.
-/
