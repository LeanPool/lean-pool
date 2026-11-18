/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.HasKEdgeColoring

/-!
# Coloring Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Finitely many edges admit a proper full coloring, even if the vertex type is infinite. -/
theorem ColoringExists {V E : Type*} [Finite E]
    (G : LooplessMultigraph V E) : ∃ k, HasKEdgeColoring G k := by
  classical
  let _ := Fintype.ofFinite E
  refine ⟨Fintype.card E, fun e => some (Fintype.equivFin E e), ?_, fun e => ?_⟩
  · intro e f c hne hadj he hf
    apply hne
    apply (Fintype.equivFin E).injective
    exact Option.some.inj (he.trans hf.symm)
  · exact ⟨Fintype.equivFin E e, rfl⟩

end GoldbergSeymour

end
