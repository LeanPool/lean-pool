/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext

public import LeanPool.GoldbergSeymour.SameGoodHierarchy

/-!
# P2752_T2_Minimum Context Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_MinimumContextTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (newBase : HierarchyBase corr.replacementETT sigma)
    (Cnew : HierarchyCounterexample newBase)
    (hsame : SameGoodHierarchy C.good Cnew.good) :
    Nonempty (HierarchyMinimumCounterexampleContext G k e0
      corr.replacementInput T sigma corr.replacementETT newBase Cnew) := by
  classical
  obtain ⟨hstar, hpath, hstage⟩ :=
    P2752_T2_HierarchyMeasures C.hierarchy Cnew.hierarchy hsame.1
  have hmeasure : HierarchyCounterexampleMeasure Cnew =
      HierarchyCounterexampleMeasure C := by
    unfold HierarchyCounterexampleMeasure
    rw [← hpath, ← hstage]
  have hcount : C.hierarchy.dividerCount = Cnew.hierarchy.dividerCount := hsame.2.choose
  have hmissing : TreeMissingColors sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
      TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl corr.terminalStability.2
  refine ⟨{
    proper := corr.coloringProperties.1
    oneEdgeUncolored := corr.coloringProperties.2
    lowerRung := ?_
    fewerDividers := ?_
    lexicographicMinimality := ?_
    largeMissingSet := ?_ }⟩
  · intro input' T' generating' lower hp hlt hm
    exact ctx.lowerRung lower hp (by simpa only [corr.rungAgreement] using hlt) hm
  · intro input' T' generating' other hr hm base' K good hdiv
    exact ctx.fewerDividers other (hr.trans corr.rungAgreement) hm base' K good
      (by simpa only [hcount] using hdiv)
  · intro input' T' generating' other base' C' hr hc
    rw [hmeasure]
    exact ctx.lexicographicMinimality C' (hr.trans corr.rungAgreement) (hc.trans hcount.symm)
  · change 2 * corr.replacementETT.rounds + 11 ≤
      (TreeMissingColors sigma
        (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)).card
    rw [corr.terminalData.1, hmissing, corr.rungAgreement]
    exact ctx.largeMissingSet

end GoldbergSeymour

end
