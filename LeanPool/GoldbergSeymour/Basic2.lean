/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Basic2TerminalPE
public import LeanPool.GoldbergSeymour.Basic2TerminalSERE

/-!
# Basic2

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem Basic2 {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∀ (delta : Fin k),
        DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
        ∀ (v : V),
          BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
          (∃ w, BoundaryColorVertex G sigma
              (TreeSequenceVertexSet Tn) delta w ∧
            TreeVertexOrder Tn w v) →
          ∀ (hvFinal : v ∈ TreeSequenceVertexSet T)
            (q : Fin ett.rounds) (vi : V),
            (ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.PE ∨
               ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.SE) →
            ett.series.data.chosenVertex q.succ = some vi →
            ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 →
            v = vi ∨ TreeVertexOrder T v vi := by
  classical
  have hterminal :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∨
        ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE := by
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    generalize htarget : n = target
    cases ett.series.certified target <;> simp_all [n]
  rcases hterminal with hterminalPE | hterminalSERE
  · exact Basic2TerminalPE G k e0 input T generating ett hMP hpositive
      hlower hterminalPE
  · exact Basic2TerminalSERE G k e0 input T generating ett hMP hpositive
      hlower hterminalSERE

end GoldbergSeymour

end
