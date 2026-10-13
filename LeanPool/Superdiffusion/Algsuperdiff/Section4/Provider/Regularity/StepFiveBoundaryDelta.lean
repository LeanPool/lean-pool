/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitLift

/-!
# StepFiveBoundaryDelta

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Provider.ExcessDecay MeasureTheory
open scoped ENNReal
open scoped Classical

noncomputable section

variable {d : ℕ}

/-! ## 1. The window average of `∇h`, and its cap -/

/-- **The window average is capped by any pointwise bound on the domain cube.**

`‖(∇h)_W‖ ≤ K` whenever `‖∇h‖ ≤ K` pointwise on `□_m ⊇ W`.  This is the `|avg
∇h| ≤ ‖∇h‖_{L^∞}` step the boundary chain uses, taken at the pointwise binder
rather than at an essential supremum. -/
theorem norm_volumeAverageVec_truncatedWindow_le_of_bound {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) {gradh : Vec d → Vec d} {K : ℝ}
    (hK : 0 ≤ K)
    (hint : ∀ i, IntegrableOn (fun y => gradh y i) (truncatedWindow z m j) volume)
    (hbd : ∀ y ∈ openCubeSet (originCube d m), ‖gradh y‖ ≤ K) :
    ‖volumeAverageVec (truncatedWindow z m j) gradh‖ ≤ K := by
  have hsub := norm_volumeAverageVec_sub_le (W := truncatedWindow z m j) (G := gradh)
    (A := 0) (K := K) (volume_truncatedWindow_pos j hz)
    (volume_truncatedWindow_lt_top z m j) hint hK
    (fun y hy => by
      simpa using hbd y (truncatedWindow_subset_domain z m j hy))
  simpa using hsub

end

end Algsuperdiff.Section4.Provider.Regularity
