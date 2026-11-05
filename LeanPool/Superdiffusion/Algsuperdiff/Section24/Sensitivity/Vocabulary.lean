/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.SealedExports
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Semantics
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.PerturbCoeffOn
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.UnitCubeBigLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationErrorCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.ValueL2
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.W1Infinity
public import LeanPool.HighContrastHomogenization.Support.Ambient.ScalarMatrix

/-!
# Vocabulary

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

