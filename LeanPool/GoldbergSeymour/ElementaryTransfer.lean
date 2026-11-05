/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DensityLowerBound
public import LeanPool.GoldbergSeymour.DensityMonotone
public import LeanPool.GoldbergSeymour.Elementary

/-!
# Elementary Transfer

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ElementaryTransfer {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (F : Finset E)
    (hχ : ChromaticIndex (RestrictEdges G F) = ChromaticIndex G)
    (hElem : Elementary (RestrictEdges G F)) : Elementary G := by
  unfold Elementary at hElem ⊢
  have lowerBound : DensityCeil G ≤ ChromaticIndex G := DensityLowerBound G
  have upperBound : ChromaticIndex G ≤ DensityCeil G := by
    calc
      ChromaticIndex G = ChromaticIndex (RestrictEdges G F) := hχ.symm
      _ = DensityCeil (RestrictEdges G F) := hElem
      _ ≤ DensityCeil G := DensityMonotone G F
  exact le_antisymm upperBound lowerBound

end GoldbergSeymour

end
