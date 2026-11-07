/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveColor
public import Mathlib.Data.Fintype.Basic

/-!
# Defective Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Colors occurring on at least two edges of the vertex-set boundary. -/
noncomputable def DefectiveColors {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (X : Finset V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun alpha => DefectiveColor G phi X alpha

end GoldbergSeymour

end
