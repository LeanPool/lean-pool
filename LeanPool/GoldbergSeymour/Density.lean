/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import LeanPool.GoldbergSeymour.DensityValue
public import LeanPool.GoldbergSeymour.EligibleOddSet

/-!
# Density

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The maximum of zero and the odd-set edge densities over eligible vertex sets. -/
noncomputable def Density {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) : ℚ
    := by
  classical
  let eligible := Finset.univ.powerset.filter fun U : Finset V => EligibleOddSet U
  let values := eligible.image (DensityValue G)
  exact (insert 0 values).max' (by simp)

end GoldbergSeymour

end
