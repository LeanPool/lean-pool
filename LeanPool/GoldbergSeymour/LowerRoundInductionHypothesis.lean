/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# Lower-round induction hypothesis

The complete six-part induction package for smaller extended Tashkinov trees.
Factored from the repeated hypotheses in Wesley Pegden’s formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Elementarity, interchangeability, stability, separation and recoloring
properties assumed for every positive smaller number of extension rounds. -/
def LowerRoundInductionHypothesis {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (rounds : ℕ) : Prop :=
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), 0 < lower.rounds → lower.rounds < rounds → MaximumProperty lower → (open
        scoped Classical in LowerRoundProperties lower)

end GoldbergSeymour

end
