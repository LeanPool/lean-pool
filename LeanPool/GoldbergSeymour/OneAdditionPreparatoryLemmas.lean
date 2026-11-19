/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Preparatory lemmas for hierarchy normalization

Extracted from Wesley Pegden’s Trellis formalization of the Goldberg–Seymour
theorem at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish
properties used in the computed hierarchy records of
    `HierarchyCounterexampleOneAdditionPositiveDividerImpossible`.
-/

@[expose] public section

namespace GoldbergSeymour.OneAdditionPreparatoryLemmas

theorem helper_hnew_2064.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (alpha theta : Fin k),
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi theta alpha (Sum.inl y);
    ∀
      (_ :
        (IsProperEdgeColoring G sigma ∧
          IsOneEdgeUncolored sigma e0 ∧
            StableColoring A (TashkinovStoredColors ett.series.data n) phi sigma ∧
              TreeColoringInvariant A phi sigma ∧
                ∀ (f : E), TreeIncidentEdge A f → sigma f = phi f))
      (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (hterminalTree :
        corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc =
          Tn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm hterminalTree),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
          Eq.mpr
            (id
              (congrArg
                (fun (_a : TreeSequence G e0) ↦
                  TreeSequenceInitialSegment _a
                    (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                hcoreT))
            H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    ∀
      (_ :
        (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
          TreeSequenceInitialSegment (H.stage j.castSucc) A))
      (a : Fin K.dividerCount),
    ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn y alpha theta sigma hstableA corrT
      baseT hcoreT hterminalTree K stageInsideA a
  ext c
  simp only [Finset.mem_biUnion]
  constructor <;> rintro ⟨v, hv, hc⟩
  · exact ⟨v, hv, by
      rw [← hstableA.2.2.2.1.2 v
        (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
          (Finset.mem_sdiff.mp hv).1)]
      exact hc⟩
  · exact ⟨v, hv, by
      rw [hstableA.2.2.2.1.2 v
        (TreeSequenceInitialSegmentVertexSetSubset (stageInsideA a.succ)
          (Finset.mem_sdiff.mp hv).1)]
      exact hc⟩

end GoldbergSeymour.OneAdditionPreparatoryLemmas

end
