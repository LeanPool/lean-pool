/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndex

/-!
# Chromatic Index Spec

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ChromaticIndexSpec {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) :
    HasKEdgeColoring G (ChromaticIndex G) ∧
      ∀ k, HasKEdgeColoring G k → ChromaticIndex G ≤ k := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · exact Nat.find_spec (ColoringExists G)
  · intro k hk
    exact Nat.find_min' (ColoringExists G) hk

end GoldbergSeymour

end
