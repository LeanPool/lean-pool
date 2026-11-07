/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.HierarchyCounterexample

/-!
# StableChangeCaseThree: supporting constructions, part 2

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.StableChangeCaseThreePreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperUniqueRefresh2220Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq V]
   [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
   (∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
     ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
       corrT.replacementETT.series.data.tree (Fin.last corrT.replacementETT.rounds).castSucc = Tn ∧
        corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
          ett.series.data.kind n ∧
         TashkinovStoredColors corrT.replacementETT.series.data
           (Fin.last corrT.replacementETT.rounds) =
          Dn),
      let K : TashkinovHierarchy corrT.replacementETT baseT :=
       {
        dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
      (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStarredStage K j = HierarchyStarredStage H j) →
       (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
        ∀ (i : Fin K.dividerCount),
         ∃! eta : Fin k,
          eta ∈ HierarchyStoredColorsAt K i.succ ∧
           (C.good.gamma i.succ eta ⊆
             (TreeSequenceVertexSet (K.stage i.succ.castSucc) \
                TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
              fun (v : V) ↦ MissingColors G sigma v) ∧
            ∀ theta ∈ HierarchyStoredColorsAt K i.succ,
             theta ≠ eta → C.good.gamma i.succ theta = C.good.gamma i.castSucc theta

theorem helper_uniqueRefresh_2220.{u_1, u_2} :
    helperUniqueRefresh2220Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn ordinaryToA missingA corrT
      baseT hcoreT terminalData K starredEq storedEq a
  have hnew :
      ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
          fun v => MissingColors G sigma v) =
      ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
          fun v => MissingColors G phi v) := by
    apply Finset.biUnion_congr rfl
    intro v hv
    exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ)
      (Finset.mem_sdiff.mp hv).1)
  change ∃! eta : Fin k,
    eta ∈ HierarchyStoredColorsAt K a.succ ∧
      C.good.gamma a.succ eta ⊆
        ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage K a.castSucc)).biUnion
            fun v => MissingColors G sigma v) ∧
      ∀ theta ∈ HierarchyStoredColorsAt K a.succ, theta ≠ eta →
        C.good.gamma a.succ theta = C.good.gamma a.castSucc theta
  rw [starredEq a.castSucc, hnew]
  simp only [storedEq]
  exact C.good.uniqueRefresh a

end GoldbergSeymour.StableChangeCaseThreePreparation

end
