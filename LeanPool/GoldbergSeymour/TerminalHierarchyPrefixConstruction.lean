/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TerminalHierarchyPrefixPreparation
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# Terminal hierarchy prefix constructors

Supporting constructions for the Goldberg–Seymour edge-coloring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalHierarchyPrefixPreparation

open scoped Sym2

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperHB477.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [ Fintype V] →
            [ Fintype E] →
              [ DecidableEq V] →
                [ DecidableEq E] →
                  (G : LooplessMultigraph V E) →
                    (k : ℕ) →
                      (e0 : E) →
                        (input : PartialEdgeColoring E k) →
                          (T : TreeSequence G e0) →
                            (generating phi : PartialEdgeColoring E k) →
                              (ett : ExtendedTashkinovTree G k e0 input T generating) →
                                (base : HierarchyBase ett phi) →
                                  (H : TashkinovHierarchy ett base) →
                                    (B : TreeSequence G e0) →
                                      (hAB :
                                          TreeSequenceInitialSegment
                                            (HierarchyStarredStage H (Fin.last H.dividerCount)) B) →
                                        (hBT : TreeSequenceInitialSegment B T) →
                                          (segmentTrans :
                                              ∀ {A B C : TreeSequence G e0}
                                                (_ : TreeSequenceInitialSegment A B)
                                                (_ : TreeSequenceInitialSegment B C),
                                                TreeSequenceInitialSegment A C) →
                                            (stageSegment :
                                                ∀ (a d : ℕ)
                                                  (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
                                                  TreeSequenceInitialSegment
                                                    (H.stage
                                                      (⟨a, by omega⟩ :
                                                        Fin (H.dividerCount + (2 : ℕ))))
                                                    (H.stage
                                                      (⟨a + d, by omega⟩ :
                                                        Fin (H.dividerCount + (2 : ℕ))))) →
                                              let lastStage : TreeSequence G e0 :=
                                                HierarchyStarredStage H (Fin.last H.dividerCount);
                                              (lastZero :
                                                  H.dividerCount = (0 : ℕ) →
                                                    lastStage = base.core) →
                                                (lastPositive :
                                                    have lastStage : TreeSequence G e0 :=
                                                      HierarchyStarredStage H
                                                        (Fin.last H.dividerCount);
                                                    H.dividerCount ≠ (0 : ℕ) →
                                                      lastStage =
                                                        H.stage
                                                          (⟨H.dividerCount, by omega⟩ :
                                                            Fin (H.dividerCount + (2 : ℕ)))) →
                                                  (lastToB :
                                                      TreeSequenceInitialSegment lastStage B) →
                                                    (firstToB :
                                                        TreeSequenceInitialSegment
                                                          (ett.series.data.tree
                                                            (Fin.last ett.rounds).castSucc)
                                                          B) →
                                                      (strictFirst :
                                                          (ett.series.data.tree
                                                                (Fin.last
                                                                    ett.rounds).castSucc).length <
                                                            B.length) →
                                                        let ettB :
                                                          ExtendedTashkinovTree G k e0 input B
                                                            generating :=
                                                          { rounds := ett.rounds,
                                                            roundsPositive := ett.roundsPositive,
                                                            series := ett.series,
                                                            abovePenultimate := firstToB,
                                                            strictAbovePenultimate := strictFirst,
                                                            belowFinal :=
                                                              segmentTrans hBT ett.belowFinal,
                                                            generatingColoring :=
                                                              ett.generatingColoring :
                                                            ExtendedTashkinovTree G k e0 input B
                                                              generating };
                                                        let baseB : HierarchyBase ettB phi := by
                                                          exact
                                                            @helperBaseB420 (@V) (@E) inferInstance
                                                              inferInstance inferInstance
                                                              inferInstance (@G) (@k) (@e0) (@input)
                                                              (@T) (@generating) (@phi) (@ett)
                                                              (@base) (@B) (@hBT) (@segmentTrans)
                                                              (@firstToB) (@strictFirst)
                                                        let hbStage :
                                                          Fin (H.dividerCount + (2 : ℕ)) →
                                                            TreeSequence G e0 :=
                                                          fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
                                                          if
                                                              (↑j : ℕ) =
                                                                H.dividerCount + (1 : ℕ) then
                                                            B
                                                          else
                                                            H.stage
                                                              (⟨(↑j : ℕ), by omega⟩ :
                                                                Fin (H.dividerCount + (2 : ℕ)));
                                                        (hbStageAt :
                                                            ∀ (j : Fin (H.dividerCount + (2 : ℕ)))
                                                              (hj : (↑j : ℕ) ≤ H.dividerCount),
                                                              hbStage j =
                                                                H.stage
                                                                  (⟨(↑j : ℕ), by omega⟩ :
                                                                    Fin
                                                                      (H.dividerCount + (2 : ℕ)))) →
                                                          (hbNested :
                                                              ∀
                                                                (j :
                                                                  Fin (H.dividerCount + (1 : ℕ))),
                                                                TreeSequenceInitialSegment
                                                                  ((fun
                                                                        (j :
                                                                          Fin
                                                                            (H.dividerCount +
                                                                              (2 : ℕ))) ↦
                                                                      if
                                                                          (↑j : ℕ) =
                                                                            H.dividerCount +
                                                                              (1 : ℕ) then
                                                                        B
                                                                      else
                                                                        H.stage
                                                                          (⟨(↑j : ℕ), by omega⟩ :
                                                                            Fin
                                                                              (H.dividerCount +
                                                                                (2 : ℕ))))
                                                                    j.castSucc)
                                                                  ((fun
                                                                        (j :
                                                                          Fin
                                                                            (H.dividerCount +
                                                                              (2 : ℕ))) ↦
                                                                      if
                                                                          (↑j : ℕ) =
                                                                            H.dividerCount +
                                                                              (1 : ℕ) then
                                                                        B
                                                                      else
                                                                        H.stage
                                                                          (⟨(↑j : ℕ), by omega⟩ :
                                                                            Fin
                                                                              (H.dividerCount +
                                                                                (2 : ℕ))))
                                                                    j.succ)) →
                                                            (hbStrict :
                                                                ∀
                                                                  (j :
                                                                    Fin (H.dividerCount + (1 : ℕ))),
                                                                  ((fun
                                                                            (j :
                                                                              Fin
                                                                                (H.dividerCount +
                                                                                  (2 : ℕ))) ↦
                                                                          if
                                                                              (↑j : ℕ) =
                                                                                H.dividerCount +
                                                                                  (1 : ℕ) then
                                                                            B
                                                                          else
                                                                            H.stage
                                                                              (⟨(↑j : ℕ), by
                                                                                  omega⟩ :
                                                                                Fin
                                                                                  (H.dividerCount +
                                                                                    (2 : ℕ))))
                                                                        j.castSucc).length <
                                                                    ((fun
                                                                            (j :
                                                                              Fin
                                                                                (H.dividerCount +
                                                                                  (2 : ℕ))) ↦
                                                                          if
                                                                              (↑j : ℕ) =
                                                                                H.dividerCount +
                                                                                  (1 : ℕ) then
                                                                            B
                                                                          else
                                                                            H.stage
                                                                              (⟨(↑j : ℕ), by
                                                                                  omega⟩ :
                                                                                Fin
                                                                                  (H.dividerCount +
                                                                                    (2 : ℕ))))
                                                                        j.succ).length) →
                                                              TashkinovHierarchy ettB baseB := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B hAB hBT segmentTrans stageSegment
      lastStage lastZero lastPositive lastToB firstToB strictFirst ettB baseB hbStage hbStageAt
      hbNested hbStrict
  exact {
    dividerCount := H.dividerCount
    stage := hbStage
    baseStage := by
      rw [show hbStage 0 = H.stage 0 by simp [hbStage]]
      simpa [ettB] using H.baseStage
    terminalStage := by simp [hbStage]
    nested := hbNested
    strict := hbStrict
    dividerPosition := fun i => ⟨(H.dividerPosition i).val, by
      have hd := H.dividerStage i
      have hi : i.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt i.isLt
      have hlastB : TreeSequenceInitialSegment
          (H.stage ⟨H.dividerCount, by omega⟩) B := by
        rw [← lastPositive (by omega)]
        exact lastToB
      have hseg := stageSegment (i.val + 1)
        (H.dividerCount - (i.val + 1)) (by omega)
      have heq : i.val + 1 + (H.dividerCount - (i.val + 1)) = H.dividerCount :=
        Nat.add_sub_of_le hi
      have hseg' : TreeSequenceInitialSegment
          (H.stage ⟨i.val + 1, by omega⟩)
          (H.stage ⟨H.dividerCount, by omega⟩) := by
        convert hseg using 1
        · congr 1
          apply Fin.ext
          exact heq.symm
      have hp := (segmentTrans hseg' hlastB).1
      have he := congrArg TreeSequence.length hd
      have he' : (H.stage ⟨i.val + 1, by omega⟩).length =
          (H.dividerPosition i).val := by
        rw [TreeSequencePrefix] at he
        simpa using he
      exact Nat.lt_succ_of_le (by
        rw [← he']
        exact hp)⟩
    dividerPositive := by intro i; exact H.dividerPositive i
    dividerIncreasing := by intro i j hij; exact H.dividerIncreasing i j hij
    dividerStage := by
      intro i
      have hi : i.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt i.isLt
      have he : hbStage ⟨i.val + 1, by omega⟩ =
          H.stage ⟨i.val + 1, by omega⟩ := by
        exact hbStageAt ⟨i.val + 1, by omega⟩ hi
      rw [he]
      have hpos :=
        @helper_hpos_300 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
            (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B) (@hAB)
            (@segmentTrans) (@stageSegment) (@lastPositive) (@i) (@hi)
      have hpref :=
        @helper_hpref_320 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
            (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@base) (@H) (@B) (@hBT)
            (@i) (@hpos)
      rw [hpref]
      simpa [ettB] using H.dividerStage i
    coreInsideFirst := by
      by_cases hc : H.dividerCount = 0
      · have he : hbStage ⟨1, by omega⟩ = B := by simp [hbStage, hc]
        rw [he]
        have hab : TreeSequenceInitialSegment base.core B := by
          have hh := hAB
          have hs : HierarchyStarredStage H (Fin.last H.dividerCount) = base.core := by
            simpa [lastStage] using lastZero hc
          rw [hs] at hh
          exact hh
        simpa [baseB] using hab
      · have he : hbStage ⟨1, by omega⟩ = H.stage ⟨1, by omega⟩ :=
        hbStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hc)
        rw [he]
        simpa [baseB] using H.coreInsideFirst }

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation904Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
   (generating phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
   (H : TashkinovHierarchy ett base) (good : GoodHierarchy H) (B : TreeSequence G e0)
   (hAB : TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount)) B)
   (hBT : TreeSequenceInitialSegment B T)
   (segmentRefl : ∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A)
   (segmentTrans :
    ∀ {A B C : TreeSequence G e0} (hAB : TreeSequenceInitialSegment A B)
     (hBC : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)
   (stageSegment :
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
     TreeSequenceInitialSegment (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
      (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))),
   let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
   ∀ (lastZero : H.dividerCount = (0 : ℕ) → lastStage = base.core)
    (lastPositive :
     have lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
     H.dividerCount ≠ (0 : ℕ) →
      lastStage = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
    (lastToB : TreeSequenceInitialSegment lastStage B)
    (firstToB : TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) B)
    (strictFirst : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < B.length),
    let ettB : ExtendedTashkinovTree G k e0 input B generating :=
     {
      rounds := ett.rounds, roundsPositive := ett.roundsPositive, series := ett.series,
      abovePenultimate := firstToB, strictAbovePenultimate := strictFirst,
      belowFinal := segmentTrans hBT ett.belowFinal, generatingColoring := ett.generatingColoring :
      ExtendedTashkinovTree G k e0 input B generating };
    ∀ (mpB : MaximumProperty ettB),
     let baseB : HierarchyBase ettB phi :=
      {
       core := base.core, closure := base.closure, supportPosition := base.supportPosition,
       supportPositive := base.supportPositive,
       terminalMissingColors := id base.terminalMissingColors,
       parallel :=
        ((Eq.symm
          (id
           (implies_congr
            (Eq.refl (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE))
            (congrArg
             (And
              (ett.series.data.chosenVertex (Fin.last ett.rounds) =
               some
                ((ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex
                 base.supportPosition)))
             (congrArg
              (And
               (TashkinovClosure phi
                (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                 (↑base.supportPosition : ℕ) base.supportPositive
                 (Nat.le_of_lt_succ base.supportPosition.isLt))
                base.closure))
              (propext nonempty_prop)))))) ▸
         (implies_congr
           (Eq.refl (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE))
           (congrArg
            (And
             (ett.series.data.chosenVertex (Fin.last ett.rounds) =
              some
               ((ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex base.supportPosition)))
            (congrArg
             (And
              (TashkinovClosure phi
               (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                (↑base.supportPosition : ℕ) base.supportPositive
                (Nat.le_of_lt_succ base.supportPosition.isLt))
               base.closure))
             (propext nonempty_prop))) ▸
          base.parallel)),
       nonparallel := id base.nonparallel : HierarchyBase ettB phi };
     let hbStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
      else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
     ∀
      (hbStageOld : ∀ (j : Fin (H.dividerCount + (1 : ℕ))), hbStage j.castSucc = H.stage j.castSucc)
      (hbStageAt :
       ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ H.dividerCount),
        hbStage j = H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
      (hbNested :
       ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment
         ((fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
           if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
           else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          j.castSucc)
         ((fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
           if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
           else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          j.succ))
      (hbStrict :
       ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        ((fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
            if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
            else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
           j.castSucc).length <
         ((fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
            if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
            else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
           j.succ).length),
      let HB : TashkinovHierarchy ettB baseB :=
       helperHB477 G k e0 input T generating phi ett base H B hAB hBT segmentTrans stageSegment
        lastZero lastPositive lastToB firstToB strictFirst hbStageAt hbNested hbStrict;
      ∀
       (stageOrdNext :
        ∀ (i : Fin H.dividerCount), HB.stage i.succ.castSucc = H.stage i.succ.castSucc)
       (starredEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStarredStage HB j = HierarchyStarredStage H j)
       (storedEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H j)
       (beforeFirstMissing :
        ∀ {A B : TreeSequence G e0} (hAB : TreeSequenceInitialSegment A B) (eta : Fin k)
         (i : Fin (A.length + (1 : ℕ))) (hiEnd : (↑i : ℕ) < A.length)
         (hi : (↑i : ℕ) < (↑(HierarchyFirstMissingPosition phi A eta) : ℕ)),
         let iB : Fin (B.length + (1 : ℕ)) := Fin.castLE (Nat.succ_le_succ hAB.1) i;
         (↑iB : ℕ) < (↑(HierarchyFirstMissingPosition phi B eta) : ℕ))
       (missingEq :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
         HierarchyStageMissingColors HB j = HierarchyStageMissingColors H j),
       ∃ (ettB : ExtendedTashkinovTree G k e0 input B generating),
        MaximumProperty ettB ∧
         ettB.rounds = ett.rounds ∧
          ettB.series ≍ ett.series ∧
           ∃ (baseB : HierarchyBase ettB phi),
            baseB.core = base.core ∧
             baseB.closure = base.closure ∧
              (↑baseB.supportPosition : ℕ) = (↑base.supportPosition : ℕ) ∧
               ∃ (HB : TashkinovHierarchy ettB baseB) (hcount : HB.dividerCount = H.dividerCount),
                (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                  HB.stage j.castSucc = H.stage (Fin.cast (by omega) j).castSucc ∧
                   HierarchyStarredStage HB j = HierarchyStarredStage H (Fin.cast (by omega) j)) ∧
                 (∀ (i : Fin HB.dividerCount),
                   (↑(HB.dividerPosition i) : ℕ) = (↑(H.dividerPosition (Fin.cast hcount i)) : ℕ)) ∧
                  ∃ (goodB : GoodHierarchy HB),
                   ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                    HierarchyStoredColorsAt HB j =
                      HierarchyStoredColorsAt H (Fin.cast (by omega) j) ∧
                     HierarchyStageMissingColors HB j =
                       HierarchyStageMissingColors H (Fin.cast (by omega) j) ∧
                      ∀ (eta : Fin k),
                       goodB.gamma j eta = good.gamma (Fin.cast (by omega) j) eta ∧
                        HierarchySegmentColors HB j eta ⊆
                         HierarchySegmentColors H (Fin.cast (by omega) j) eta

end GoldbergSeymour.TerminalHierarchyPrefixPreparation

end
