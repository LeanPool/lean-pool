/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Measurability
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.LipschitzBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Integrals
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.BlockEnergyAverage
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.MuObservable

/-!
# Coarse-graining support: Support.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

Pure-import umbrella for the five-file `FixedCompetitorEnergyMeasurability`
chain.

**Internal claim of the chain (read top-down):** lift `PointwiseLocalSigma` scalar
atoms (`Measurability`) → fixed-coefficient Borel maps on `HilbertMat`
(`LipschitzBounds`) → quantitative-slice integral algebra (`Integrals`) →
measurable block-energy averages (`BlockEnergyAverage`) → measurability of
the `Mu` candidate as a coefficient-field functional (`MuObservable`).

**Consumed by:** `Internal/AEESliceAssembly/{BlockEnergyAverage,
MuFamily}.lean`, then `Theorems/Mu.lean :: aemeasurable_Mu_cubeSet`.

If a sixth file becomes necessary in this chain, that is the signal to
refactor rather than extend, per the rebuild contract.
-/
