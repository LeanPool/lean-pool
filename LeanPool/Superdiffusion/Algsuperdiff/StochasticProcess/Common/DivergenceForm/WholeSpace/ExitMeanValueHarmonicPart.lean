/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValue
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicPotential

/-!
# ExitMeanValueHarmonicPart

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The uniform bound of the residual datum on an exhaustion cube

The vanishing-shift family of the exit decomposition is rewritten by linearity
of the Dirichlet resolvent in its datum, against the *residual* `g - mu psi`
restricted to the cube, which does not depend on the shift.  This file records
the uniform bound that residual obeys, `cubeResolventResidualBound`, together
with its nonnegativity.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The residual datum -/

/-- The uniform bound of the residual datum. -/
def cubeResolventResidualBound (R : PositiveC0ContractiveResolvent (Vec d))
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) : ℝ :=
  ‖g‖ + (mu : ℝ) * ‖R.toContractiveResolvent.operator mu g‖

theorem cubeResolventResidualBound_nonneg (R : PositiveC0ContractiveResolvent (Vec d))
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    0 ≤ cubeResolventResidualBound R mu g :=
  add_nonneg (norm_nonneg g) (mul_nonneg mu.property.le (norm_nonneg _))

variable [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

variable (R : PositiveC0ContractiveResolvent (Vec d))

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
