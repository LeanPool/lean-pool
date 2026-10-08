/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.Setup
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.CorrectionSpaceBasic
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.RecoveryPackages

/-!
# Coarse-graining support: Support.CoarseGraining.MuRecovery

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Mu recovery (aggregate re-export)

Previously a 2111-line monolithic module whose MuCorrectionSpaceRecoveryData
namespace alone spanned ~1560 lines; now split along namespace / theme
boundaries into the five files imported above. Shim for backward
compatibility.
-/
