/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Perturbation.Integrand
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Perturbation.PairHalfScalar
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Perturbation.VolumeAverage
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Perturbation.BlockEnergyFirstVariation
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Perturbation.ResponseJMuAdjoint

/-!
# Coarse-graining support: Support.CoarseGraining.BlockResponse.Perturbation

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# BlockResponse perturbation, first-variation, and witness identities
(aggregate re-export)

Previously a 2169-line monolithic module; now split along thematic
boundaries into the five files imported above. Shim for backward compatibility.
-/
