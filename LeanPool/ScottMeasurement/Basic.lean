/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.FinHead
public import LeanPool.ScottMeasurement.LinearInequalities.Definitions
public import LeanPool.ScottMeasurement.LinearInequalities.Separation
public import LeanPool.ScottMeasurement.LinearInequalities.Rationalization
public import LeanPool.ScottMeasurement.LinearInequalities.Sequences
public import LeanPool.ScottMeasurement.LinearInequalities.ScottTheorems
public import LeanPool.ScottMeasurement.LinearInequalities.OrderedGroup
public import LeanPool.ScottMeasurement.Preference.Direct
public import LeanPool.ScottMeasurement.Preference.Cycle
public import LeanPool.ScottMeasurement.Preference.Intransitive
public import LeanPool.ScottMeasurement.Differences.Pair
public import LeanPool.ScottMeasurement.Differences.Ordered
public import LeanPool.ScottMeasurement.Probability.Basic
public import LeanPool.ScottMeasurement.Probability.Atoms
public import LeanPool.ScottMeasurement.Probability.Finite
public import LeanPool.ScottMeasurement.Probability.KPSCounterexample
public import LeanPool.ScottMeasurement.Probability.Infinite.EventSpace
public import LeanPool.ScottMeasurement.Probability.Infinite.HahnBanach
public import LeanPool.ScottMeasurement.Probability.Infinite.Kelley
public import LeanPool.ScottMeasurement.Probability.Infinite.Reconstructed

/-!
# Scott 1964 — Measurement Structures and Linear Inequalities

Primary source: Dana S. Scott, *Measurement Structures and Linear
Inequalities*, Journal of Mathematical Psychology 1 (1964), 233–247.
Working transcription: `sources/ScottMeasurement1964_vision.md`.

The paper applies the general solvability criterion for finite systems of
linear inequalities (Theorems 1.1–1.4) to three measurement problems:
intransitive indifference (Theorem 2.1), ordered differences (Theorems 3.1
and 3.2), and subjective probability (Theorem 4.1).

This module re-exports the complete sorry-free development imported by
`Solution.lean`: Scott's eight published theorems, the finite KPS
counterexample, and the separately labelled modern reconstruction of the
infinite probability theorem.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

end Scott1964.MeasurementStructures
