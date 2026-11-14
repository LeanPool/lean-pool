/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.NormalTripleTrunk

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

public import LeanPool.GoldbergSeymour.TreeUsedColors

/-!
# Scheide Balanced Candidate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A Tashkinov tree preserving the normal trunk and used colors, with odd order and paired later
edge colors.
-/
structure ScheideBalancedCandidate {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
  {T : TreeSequence G e0} (N : NormalGlobalMaximumTriple G k e0 phi T) (S : TreeSequence G e0) :
  Prop where
 tashkinov : TashkinovTree G e0 phi S
 oddOrder : Odd (TreeSequenceVertexSet S).card
 exactTrunk : TreeSequenceInitialSegment (NormalTripleTrunk N) S
 usedColors : TreeUsedColors phi S ⊆ TreeUsedColors phi T
 paired :
  ∀ j : ℕ,
   ∀ hlow : N.height < 2 * j,
    ∀ hupp : 2 * j < S.length + 1,
     phi (S.edge ⟨2 * j - 2, by omega⟩) = phi (S.edge ⟨2 * j - 1, by omega⟩)

end GoldbergSeymour

end
