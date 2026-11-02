/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.PerturbCoeffOn
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.BigLambda.UnitCubeBigLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationErrorCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.GradientW1Infinity
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.ValueL2
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.W1Infinity
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.BoundedField
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.Existence
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.Polarization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.ResponsePairing
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.BigLambda.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.EllipticityLocality
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationError.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.HomogenizationErrorLocality
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.Characterization
public import LeanPool.HighContrastHomogenization.Support.Ambient.ScalarMatrix

/-!
# Semantics

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 2.4 sensitivity: semantic import hub for provider modules

Import hub collecting the proved semantic units (frozen definition and
characterization files together with the public Section 2.4 A modules) needed
by the Section 2.4 sensitivity provider modules.

## Cycle-safety rule

Provider modules import this file, never
`Algsuperdiff.Section24.Sensitivity.Vocabulary`.  `Vocabulary` is imported by
the frozen sensitivity anchors, so a provider importing it (directly or
transitively) would create an import cycle when the anchors are onto their
providers.  Accordingly, this file must never import `Vocabulary` or any frozen
sensitivity anchor (`ResponseJDerivative`, `CoarseMatrixDerivativeBound`,
`LambdaSensitivity`, `ResponseJSensitivity`, `BigLambdaSensitivity`,
`BigLambdaSensitivityAtDelta`, `LambdaSensitivityUnconditional`,
`ResponseJSensitivityUnconditional`).
-/
