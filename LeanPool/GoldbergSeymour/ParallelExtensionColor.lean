/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TashkinovSeriesData

/-!
# Parallel Extension Color

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An available color selected according to the latest prior parallel extension at the support
vertex.
-/
def ParallelExtensionColor {V E : Type*} [Fintype E] {G : LooplessMultigraph V E}
  {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0) (i : Fin (rounds + 1))
  (selected : PartialEdgeColoring E k) (v : V) (gamma : Fin k) : Prop :=
 gamma ∈ MissingColors G selected v ∧
  ((∃ h : Fin (rounds + 1),
    0 < h.val ∧
     h.val ≤ i.val ∧
      data.kind h = some TashkinovExtensionKind.PE ∧
       data.chosenVertex h = some v ∧
        data.delta h = some gamma ∧
         ∀ j : Fin (rounds + 1),
          0 < j.val →
           j.val ≤ i.val →
            data.kind j = some TashkinovExtensionKind.PE →
             data.chosenVertex j = some v → j.val ≤ h.val) ∨
   (∀ h : Fin (rounds + 1),
    0 < h.val →
     h.val ≤ i.val → data.kind h = some TashkinovExtensionKind.PE → data.chosenVertex h ≠ some v))

end GoldbergSeymour

end
