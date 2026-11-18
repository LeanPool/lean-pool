/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.SimplePredictableRefineInvariance
public import LeanPool.KLS.LevyStochCalc.Brownian.SimplePredictableRefineCommon
public import LeanPool.KLS.LevyStochCalc.Brownian.SimplePredictableRefineAppend

/-!
# SimplePredictable refinement and the diff-isometry on simple integrals

Refining a `SimplePredictable` integrand onto a finer partition
(`SimplePredictable.refine`), the common refinement of two simple predictables
(`commonRefinement`), and the resulting difference-isometry on simple integrals
(`diff_isometry_simple`) plus the Cauchy property for an L²-dense approximating
sequence (`cauchy_of_L2_dense_simple`). These feed the L²-completion of the
Brownian Itô integral in `Brownian/ItoL2Completion.lean`.

The material is organised in three modules, all re-exported here:
`Brownian/SimplePredictableRefineInvariance.lean` (refinement onto a finer
partition and invariance of the simple integral),
`Brownian/SimplePredictableRefineCommon.lean` (common refinement of two simple
predictables, the difference isometry and the Cauchy property) and
`Brownian/SimplePredictableRefineAppend.lean` (zero-extension to a larger
horizon).
-/
