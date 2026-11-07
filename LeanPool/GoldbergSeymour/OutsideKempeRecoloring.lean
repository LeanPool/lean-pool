/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Outside Kempe Recoloring

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A coloring obtained by swapping a fixed color pair on components disjoint from the tree. -/
def OutsideKempeRecoloring {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
  (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (alpha beta : Fin k) : Prop := by
 classical
  exact
  alpha ≠ beta ∧
   ∃ roots : Finset (Sum V E),
    (∀ z ∈ roots,
      ∀ v : V, Sum.inl v ∈ TwoColorComponent G phi alpha beta z → v ∉ TreeSequenceVertexSet T) ∧
     ∀ f : E,
      sigma f =
       if ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha beta z then
        if phi f = some alpha then some beta else if phi f = some beta then some alpha else phi f
       else phi f

end GoldbergSeymour

end
