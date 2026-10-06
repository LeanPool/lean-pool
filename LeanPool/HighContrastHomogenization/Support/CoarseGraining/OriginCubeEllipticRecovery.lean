/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.Setup
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.Translate
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.MuGeVecDot
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.Subadditivity

/-!
# Coarse-graining support: Support.CoarseGraining.OriginCubeEllipticRecovery

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Origin-cube elliptic recovery (aggregate re-export)

Previously a 2296-line monolithic module; now split along thematic boundaries
into the files imported above. This shim re-exports everything so
existing consumers keep working unchanged.
-/
