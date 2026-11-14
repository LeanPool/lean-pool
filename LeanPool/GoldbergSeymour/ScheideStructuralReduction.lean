/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideStructuralReducedAssembly
public import LeanPool.GoldbergSeymour.ScheideStructuralReordering

public import LeanPool.GoldbergSeymour.ScheideStructuralSelection

/-!
# Scheide Structural Reduction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideStructuralReduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) :
    ∃ (T' : TreeSequence G e0)
      (R : ScheideReducedConfiguration G k e0 phi T'),
      TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
      (∀ i : Fin C.s,
        (∃ r : Fin R.s, C.gamma i = R.gamma r ∧
          ∀ j : Fin 2, C.blockVertex i j = R.blockVertex r j ∧
            C.blockEdge i j = R.blockEdge r j) ∨
        ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
  classical
  obtain ⟨D⟩ := ScheideStructuralSelection G k e0 phi T C
  obtain ⟨T', ⟨Q⟩⟩ := ScheideStructuralReordering G k e0 phi T C D
  exact ⟨T', ScheideStructuralReducedAssembly G k e0 phi T C D T' Q⟩

end GoldbergSeymour

end
