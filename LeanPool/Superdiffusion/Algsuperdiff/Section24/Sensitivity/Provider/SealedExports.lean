/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.BigLambda.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BoundProvider
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.LambdaUnconditional.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Response.Closure
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.ResponseUnconditional.Provider

/-!
# SealedExports

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# sensitivity provider exports

It is imported by `Algsuperdiff.Section24.Sensitivity.Vocabulary`, which the
frozen theorems import, so a anchor closes by exact application of its
provider.

- `Provider.Path.Closure`: `responseJ_derivative` (`S24-S).
- `Provider.DhBound.Discharge.BoundProvider`: `coarseMatrixDerivative_bound`
  (`S24-S).
- `Provider.Lambda.Closure`: `lambda_sensitivity` (`S24-S).
- `Provider.Response.Closure`: `responseJ_sensitivity` (`S24-S).
- `Provider.BigLambda.Closure`: `bigLambda_sensitivity` and
  `bigLambda_sensitivity_at_delta` (`S24-S, `S24-S).
- `Provider.LambdaUnconditional.Closure`: `lambda_sensitivity_unconditional`
  (`S24-S).
- `Provider.ResponseUnconditional.Provider`:
  `responseJ_sensitivity_unconditional` (`S24-S).
-/
