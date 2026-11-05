/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration

/-!
# Scheide Structural Selection Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A partition of structural blocks into absorbed blocks and blocks selected by exit vertices. -/
structure ScheideStructuralSelectionData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) where
  /-- The number of blocks absorbed into the reordered base. -/
  absorbedCount : ℕ
  /-- The number of blocks retained as paired blocks. -/
  retainedCount : ℕ
  /-- The enumeration of exit vertices by the retained-block indices. -/
  exitEquiv : Fin retainedCount ≃ { v : V // v ∈ ScheideExitVertices T phi }
  /-- The original block index selected for each retained block. -/
  retained : Fin retainedCount → Fin C.s
  retained_injective : Function.Injective retained
  retained_missing :
    ∀ t : Fin retainedCount, C.gamma (retained t) ∈ MissingColors G phi (exitEquiv t).1
  selected_unique :
    ∀ (t t' : Fin retainedCount),
      C.gamma (retained t') ∈ MissingColors G phi (exitEquiv t).1 → t' = t
  /-- The enumeration of original blocks not selected as retained blocks. -/
  absorbedEquiv : Fin absorbedCount ≃ { i : Fin C.s // i ∉ Set.range retained }
  count_eq : C.s = absorbedCount + retainedCount
  exit_count_eq : retainedCount = (ScheideExitVertices T phi).card
  partition :
    ∀ i : Fin C.s,
      (∃! h : Fin absorbedCount, (absorbedEquiv h).1 = i) ∨
        (∃! t : Fin retainedCount, retained t = i)

end GoldbergSeymour

end
