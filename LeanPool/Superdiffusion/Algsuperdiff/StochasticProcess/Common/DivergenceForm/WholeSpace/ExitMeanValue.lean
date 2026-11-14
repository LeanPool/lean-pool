/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCube

/-!
# ExitMeanValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Nonnegativity of the one-point extension

The exit decomposition of a resolvent datum is an extended-real statement, so
it is carried by nonnegative continuous data vanishing at infinity.  This file
records the one fact about the one-point extension that the decomposition
needs: the extension of a nonnegative function is nonnegative, at the added
point as well as on the live space.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The zero extension of a nonnegative observable is nonnegative. -/
theorem onePointRealExtension_nonneg {X : Type*} {f : X → ℝ} (hf : ∀ y, 0 ≤ f y)
    (z : OnePoint X) : 0 ≤ onePointRealExtension f z := by
  induction z using OnePoint.rec with
  | infty => rw [onePointRealExtension_infty]
  | coe y => rw [onePointRealExtension_coe]; exact hf y

variable [NeZero d]

namespace WholeSpaceAnalyticData

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
