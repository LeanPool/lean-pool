/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/-
Upstream NOTICE for the matching-rates subproject

C196 v0.3 manuscript and Lean formalization
Copyright 2026 Mark Gladden

The included manuscript PDF and the Lean code are distributed under the Apache License, Version 2.0.
Mark Gladden is the responsible maintainer. AI produced the Lean proofs under his direction.

Lean source: VanGogh7777/c196-lean, matching-rates subproject.
Commit: f14c11cca549acba4a3fcf832e7af005d2afd8ee
-/

module

public import LeanPool.VenNullClockRoundRates.Filter
public import LeanPool.VenNullClockRoundRates.Finite
public import LeanPool.VenNullClockRoundRates.Geometry
public import LeanPool.VenNullClockRoundRates.Layer
public import LeanPool.VenNullClockRoundRates.Lower
public import LeanPool.VenNullClockRoundRates.Pole
public import LeanPool.VenNullClockRoundRates.RoundAreaBridge
public import LeanPool.VenNullClockRoundRates.RoundAreaCutoffInputs
public import LeanPool.VenNullClockRoundRates.RoundAreaPositiveStrips
public import LeanPool.VenNullClockRoundRates.RoundAreaUpperHemisphere
public import LeanPool.VenNullClockRoundRates.SphereModel
public import LeanPool.VenNullClockRoundRates.VenRateUpperAssembly
public import LeanPool.VenNullClockRoundRates.VenRateUpperBudget
public import LeanPool.VenNullClockRoundRates.VenRateUpperBump
public import LeanPool.VenNullClockRoundRates.VenRateUpperClassGap
public import LeanPool.VenNullClockRoundRates.VenRateUpperHeight
public import LeanPool.VenNullClockRoundRates.VenRateUpperPhysical
public import LeanPool.VenNullClockRoundRates.VenRateUpperPositive
public import LeanPool.VenNullClockRoundRates.VenRateUpperRoundRates
public import LeanPool.VenNullClockRoundRates.VenRateUpperStrips
public import LeanPool.VenNullClockRoundRates.VenRateUpperTaylor

/-!
# Matching masking rates for two-layer scans on normalized round area

Source: url:https://github.com/VanGogh7777/c196-lean/blob/4f45e33dc5376b362e13601adee77a0a76358387/paper/C196_v0.3.pdf
Authors: Mark Gladden
Status: verified
Main declarations: `VenRateUpper.matching_round_class_rates`,
  `VenRateUpper.smooth_round_common_profile_error`
Tags: inverse problems, spherical measure, moment cancellation, Laplace transforms
MSC: 28A25, 44A10
-/
