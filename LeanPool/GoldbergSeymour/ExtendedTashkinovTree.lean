/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Extended Tashkinov Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A tree lying strictly above the penultimate tree and below the final tree of a certified
extension series.
-/
structure ExtendedTashkinovTree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k) where
  /-- The positive number of extension rounds. -/
  rounds : ℕ
  roundsPositive : 1 ≤ rounds
  /-- The extension series witnessing this extended tree. -/
  series : TashkinovSeries G k rounds e0 input
  abovePenultimate : TreeSequenceInitialSegment (series.data.tree ⟨rounds, by omega⟩) T
  strictAbovePenultimate : (series.data.tree ⟨rounds, by omega⟩).length < T.length
  belowFinal : TreeSequenceInitialSegment T (series.data.tree (Fin.last (rounds + 1)))
  generatingColoring : generating = series.data.coloring (Fin.last rounds)

end GoldbergSeymour

end
