/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GeneralHighIndexElementary

/-!
# Thm GS

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ThmGS {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G) := by
  classical
  by_cases hbound : ChromaticIndex G ≤ MaximumDegree G + 1
  · exact le_max_of_le_left hbound
  · have hhigh : MaximumDegree G + 2 ≤ ChromaticIndex G := by
      omega
    have helementary : Elementary G := GeneralHighIndexElementary G hhigh
    have hequality : ChromaticIndex G = DensityCeil G := helementary
    rw [hequality]
    exact le_max_of_le_right (le_refl _)

end GoldbergSeymour

end
