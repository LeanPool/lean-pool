/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.SectorReflectionBox
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.GradientScaleReadout

/-!
# BoxGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Gap scales and snapped centres for axis cubes

This file isolates the finite-dimensional geometry used to pass from estimates
centred on cube faces to estimates centred at arbitrary points of the cube.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity

open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- Every point of an open axis cube belongs to its coordinatewise closure. -/
theorem axisCube_subset_closureSet (z : Vec d) (L : ℝ) :
    axisCube z L ⊆ {x | MemAxisCubeClosure z L x} := by
  intro x hx i
  have hi := mem_axisCube_iff.mp hx i
  exact ⟨hi.1.le, hi.2.le⟩

end

end Algsuperdiff.StochasticProcess.Common.Regularity
