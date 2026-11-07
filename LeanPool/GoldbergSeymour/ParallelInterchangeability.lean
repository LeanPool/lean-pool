/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.InterchangePEMixedCore

/-!
# interchange

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem interchange {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    (alpha ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.closure sigma alpha beta) ∧
    (alpha ∈ TreeMissingColors sigma Tn →
      TreeInterchangeable G Tn sigma alpha beta) ∧
    (alpha ∈ TreeMissingColors sigma base.core →
      TreeColorSetClosed G sigma base.core {alpha} →
      TreeInterchangeable G base.core sigma alpha beta) ∧
    (alpha ∈ TreeMissingColors sigma Tn →
      beta ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.core sigma alpha beta) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact InterchangePEClosureConstituent G k e0 input T generating sigma
      ett hMP hpositive hlower hPE base hproper hone hstable alpha beta
  · exact InterchangePETreeConstituent G k e0 input T generating sigma
      ett hMP hpositive hlower hPE base hproper hone hstable alpha beta
  · exact InterchangePEClosedCore G k e0 input T generating sigma
      ett hMP hpositive hlower hPE base hproper hone hstable alpha beta
  · exact InterchangePEMixedCore G k e0 input T generating sigma
      ett hMP hpositive hlower hPE base hproper hone hstable alpha beta

end GoldbergSeymour

end
