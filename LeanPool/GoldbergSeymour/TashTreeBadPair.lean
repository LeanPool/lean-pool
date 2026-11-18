/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Tash Tree Bad Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A critical coloring triple with a non-elementary Tashkinov tree. -/
def TashTreeBadPair {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
  (T : TreeSequence G e0) : Prop :=
 KTriple G k e0 phi ∧
  TashkinovTree G e0 phi T ∧ ¬ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)

end GoldbergSeymour

end
