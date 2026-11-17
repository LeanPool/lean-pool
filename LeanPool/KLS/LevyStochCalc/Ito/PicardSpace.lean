/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpaceDiscrete
public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpaceBieleckiEDist
public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpaceBieleckiQuotient

/-!
# The complete metric space of bounded processes

This file equips the space `SBoundedProcess` of L²-sup-bounded adapted
processes (from `Picard.lean`) with the metric structure needed to apply
Banach's fixed-point theorem to the Picard map.

## Contents

* A discrete metric and the resulting `MetricSpace` / `CompleteSpace`
  instances on `SBoundedProcess`.
* `bieleckiEDist`, `SBoundedProcess.WithBielecki` — the Bielecki-weighted
  extended pseudometric and its carrier type, and the almost-everywhere
  quotient `SBoundedProcess.AEQuot` on which it becomes a genuine
  `EMetricSpace`.
The existence/uniqueness statement itself is `Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn`
in `Ito/PicardWellPosed.lean`. The section note "The `IsRegular` hypothesis and the `S²` norm"
records why that theorem takes `IsRegular`, why the Bielecki norm is not the `S²` norm, and
where each step of the Picard chain lives.

The Banach fixed-point conclusion is in `PicardFixedPoint.lean`.

## Parts

* `Ito/PicardSpaceDiscrete.lean` — the constant-zero witness, the discrete distance and the
  `MetricSpace` / `CompleteSpace` instances on `SBoundedProcess`.
* `Ito/PicardSpaceBieleckiEDist.lean` — Euclidean Minkowski on `Fin n → ℝ`, subadditivity of
  `bieleckiNorm`, and the pseudo-edist `bieleckiEDist` with its diagonal and symmetry laws.
* `Ito/PicardSpaceBieleckiQuotient.lean` — `SBoundedProcess.WithBielecki`, the triangle
  inequality and the `PseudoEMetricSpace` instance, the separation quotient
  `SBoundedProcess.AEQuot`, and nonemptiness of both.
-/
