/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.GoodHierarchyPrefixPreparation

public import LeanPool.GoldbergSeymour.HierarchyStarredStage

/-!
# Terminal hierarchy prefix preparation

Supporting constructions for the Goldberg–Seymour edge-coloring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalHierarchyPrefixPreparation

open scoped Sym2

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_segmentTrans_81.{u_1, u_2} :
    SharedFacts.GoodHierarchyPrefixPreparation.segmentTransStatement.{u_1, u_2} :=
  SharedFacts.GoodHierarchyPrefixPreparation.segmentTrans.{u_1, u_2}

theorem helper_stageSegment_94.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (_ : TreeSequence G e0),
    (∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A) →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
      (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B segmentRefl segmentTrans a d
  induction d with
  | zero => intro h; simpa using segmentRefl (H.stage ⟨a, by omega⟩)
  | succ d ih =>
    intro h
    have hp := ih (by omega)
    have hn := H.nested ⟨a + d, by omega⟩
    have hn' : TreeSequenceInitialSegment
        (H.stage ⟨a+d, by omega⟩) (H.stage ⟨a+(d+1), by omega⟩) := by
      simpa [Nat.add_assoc] using hn
    exact segmentTrans hp hn'

theorem helper_lastPositive_115.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (_ : TreeSequence G e0),
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    H.dividerCount ≠ (0 : ℕ) →
    lastStage = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B lastStage h
  unfold lastStage HierarchyStarredStage
  obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
  · have hz : H.dividerCount = 0 := by
      simpa using congrArg Fin.val hzero
    exact False.elim (h hz)
  · rw [hi]
    simp only [Fin.cases_succ]
    congr 1
    apply Fin.ext
    simpa using (congrArg Fin.val hi).symm

theorem helper_stageLastPositive_128.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (_ : TreeSequence G e0),
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    (H.dividerCount ≠ (0 : ℕ) →
        lastStage = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    H.dividerCount ≠ (0 : ℕ) →
    H.stage (Fin.last H.dividerCount).castSucc = lastStage := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B lastStage lastPositive hp
  rw [lastPositive hp]
  apply congrArg H.stage
  apply Fin.ext
  simp

theorem helper_stageToLast_135.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (_ : TreeSequence G e0),
    (∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A) →
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    (H.dividerCount = (0 : ℕ) → lastStage = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        lastStage = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      lastStage := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B segmentRefl stageSegment lastStage
      lastZero lastPositive
  by_cases hq : H.dividerCount = 0
  · by_cases hk : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hk
      rw [lastZero hq]
      exact u.leftSegment
    · have hc : base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc :=
        base.nonparallel hk
      rw [lastZero hq, hc]
      exact segmentRefl _
  · have hs := stageSegment 0 H.dividerCount (by omega)
    rw [lastPositive hq]
    rw [← H.baseStage]
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> simp

theorem helper_hbNested_194.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (B : TreeSequence G e0),
    TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount)) B →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    (H.dividerCount ≠ (0 : ℕ) → H.stage (Fin.last H.dividerCount).castSucc = lastStage) →
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        lastStage →
    let hbStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
      else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))), hbStage j.castSucc = H.stage j.castSucc) →
    hbStage (Fin.last (H.dividerCount + (1 : ℕ))) = B →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ H.dividerCount),
        hbStage j = H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (hbStage j.castSucc) (hbStage j.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B hAB segmentTrans lastStage
      stageLastPositive stageToLast hbStage hbStageOld hbStageLast hbStageAt j
  by_cases hj : j.val = H.dividerCount
  · have hlast : j = Fin.last H.dividerCount := by
      apply Fin.ext
      simpa using hj
    rw [hlast]
    rw [hbStageOld (Fin.last H.dividerCount)]
    have hjs : (Fin.last H.dividerCount).succ = Fin.last (H.dividerCount + 1) := by rfl
    rw [hjs, hbStageLast]
    by_cases hc : H.dividerCount = 0
    · have hs0 : TreeSequenceInitialSegment (H.stage 0) lastStage := by
        simpa [H.baseStage] using stageToLast
      have hab : TreeSequenceInitialSegment lastStage B := by
        change TreeSequenceInitialSegment lastStage B at hAB
        exact hAB
      have hidx : H.stage (Fin.last H.dividerCount).castSucc = H.stage 0 := by
        congr 1
        apply Fin.ext
        simp [hc]
      rw [hidx]
      exact segmentTrans hs0 hab
    · rw [stageLastPositive hc]
      exact hAB
  · have hjlt : j.val < H.dividerCount := by omega
    have hsucc : j.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt hjlt
    rw [hbStageAt j.castSucc (Nat.le_of_lt_succ j.isLt),
      hbStageAt j.succ hsucc]
    have hn := H.nested ⟨j.val, by omega⟩
    convert hn using 1

theorem helper_hbStrict_225.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (B : TreeSequence G e0),
    (HierarchyStarredStage H (Fin.last H.dividerCount)).length < B.length →
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    (H.dividerCount ≠ (0 : ℕ) → H.stage (Fin.last H.dividerCount).castSucc = lastStage) →
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        lastStage →
    let hbStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then B
      else H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))), hbStage j.castSucc = H.stage j.castSucc) →
    hbStage (Fin.last (H.dividerCount + (1 : ℕ))) = B →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))) (hj : (↑j : ℕ) ≤ H.dividerCount),
        hbStage j = H.stage (⟨(↑j : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (hbStage j.castSucc).length < (hbStage j.succ).length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B hABstrict lastStage
      stageLastPositive stageToLast hbStage hbStageOld hbStageLast hbStageAt j
  by_cases hj : j.val = H.dividerCount
  · have hlast : j = Fin.last H.dividerCount := by
      apply Fin.ext
      simpa using hj
    rw [hlast]
    rw [hbStageOld (Fin.last H.dividerCount)]
    have hjs : (Fin.last H.dividerCount).succ = Fin.last (H.dividerCount + 1) := by rfl
    rw [hjs, hbStageLast]
    by_cases hc : H.dividerCount = 0
    · have hs0 : TreeSequenceInitialSegment (H.stage 0) lastStage := by
        simpa [H.baseStage] using stageToLast
      have hlen : lastStage.length < B.length := hABstrict
      have hidx : H.stage (Fin.last H.dividerCount).castSucc = H.stage 0 := by
        congr 1
        apply Fin.ext
        simp [hc]
      rw [hidx]
      exact lt_of_le_of_lt hs0.1 hlen
    · rw [stageLastPositive hc]
      exact hABstrict
  · have hjlt : j.val < H.dividerCount := by omega
    have hsucc : j.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt hjlt
    rw [hbStageAt j.castSucc (Nat.le_of_lt_succ j.isLt),
      hbStageAt j.succ hsucc]
    have hn := H.strict ⟨j.val, by omega⟩
    convert hn using 1;

theorem helper_hpos_300.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (B : TreeSequence G e0),
    TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount)) B →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    let lastStage : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    (H.dividerCount ≠ (0 : ℕ) →
        lastStage = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    ∀ (i : Fin H.dividerCount),
    (↑i : ℕ) + (1 : ℕ) ≤ H.dividerCount →
    (↑(H.dividerPosition i) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B hAB segmentTrans stageSegment
      lastStage lastPositive i hi
  have hs := stageSegment (i.val + 1)
    (H.dividerCount - (i.val + 1)) (by omega)
  have hs' : TreeSequenceInitialSegment
      (H.stage ⟨i.val + 1, by omega⟩)
      (H.stage ⟨H.dividerCount, by omega⟩) := by
    convert hs using 1
    apply congrArg H.stage
    apply Fin.ext
    exact (Nat.add_sub_of_le hi).symm
  have hab : TreeSequenceInitialSegment
      (H.stage ⟨H.dividerCount, by omega⟩) B := by
    rw [← lastPositive (by omega)]
    exact hAB
  have hsB := (segmentTrans hs' hab).1
  have hlen := congrArg TreeSequence.length (H.dividerStage i)
  rw [TreeSequencePrefix] at hlen
  have hval : (H.stage ⟨i.val + 1, by omega⟩).length =
      (H.dividerPosition i).val := by simpa using hlen
  omega

/-- Typed data construction shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperBaseB420.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [Fintype V] →
            [Fintype E] →
              [DecidableEq V] →
                [DecidableEq E] →
                  (G : LooplessMultigraph V E) →
                    (k : ℕ) →
                      (e0 : E) →
                        (input : PartialEdgeColoring E k) →
                          (T : TreeSequence G e0) →
                            (generating phi : PartialEdgeColoring E k) →
                              (ett : ExtendedTashkinovTree G k e0 input T generating) →
                                (base : HierarchyBase ett phi) →
                                  (B : TreeSequence G e0) →
                                    (hBT : TreeSequenceInitialSegment B T) →
                                      (segmentTrans :
                                          ∀ {A B C : TreeSequence G e0}
                                            (_ : TreeSequenceInitialSegment A B)
                                            (_ : TreeSequenceInitialSegment B C),
                                            TreeSequenceInitialSegment A C) →
                                        (firstToB :
                                            TreeSequenceInitialSegment
                                              (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                                              B) →
                                          (strictFirst :
                                              (ett.series.data.tree
                                                    (Fin.last ett.rounds).castSucc).length <
                                                B.length) →
                                            let ettB :
                                              ExtendedTashkinovTree G k e0 input B generating :=
                                              { rounds := ett.rounds,
                                                roundsPositive := ett.roundsPositive,
                                                series := ett.series, abovePenultimate := firstToB,
                                                strictAbovePenultimate := strictFirst,
                                                belowFinal := segmentTrans hBT ett.belowFinal,
                                                generatingColoring := ett.generatingColoring :
                                                ExtendedTashkinovTree G k e0 input B generating };
                                            HierarchyBase ettB phi := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T generating phi ett base B hBT segmentTrans
      firstToB strictFirst ettB
  exact {
    core := base.core, closure := base.closure,
    supportPosition := base.supportPosition,
    supportPositive := base.supportPositive,
    terminalMissingColors := id base.terminalMissingColors,
    parallel :=
      ((Eq.symm
          (id
            (implies_congr
              (Eq.refl
                (ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.PE))
              (congrArg
                (And
                  (ett.series.data.chosenVertex
                      (Fin.last ett.rounds) =
                    some
                      ((ett.series.data.tree
                            (Fin.last ett.rounds).castSucc).vertex
                        base.supportPosition)))
                (congrArg
                  (And
                    (TashkinovClosure phi
                      (TreeSequencePrefix
                        (ett.series.data.tree
                          (Fin.last ett.rounds).castSucc)
                        (↑base.supportPosition : ℕ)
                        base.supportPositive
                        (Nat.le_of_lt_succ base.supportPosition.isLt))
                      base.closure))
                  (propext nonempty_prop)))))) ▸
        (implies_congr
            (Eq.refl
              (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE))
            (congrArg
              (And
                (ett.series.data.chosenVertex (Fin.last ett.rounds) =
                  some
                    ((ett.series.data.tree
                          (Fin.last ett.rounds).castSucc).vertex
                      base.supportPosition)))
              (congrArg
                (And
                  (TashkinovClosure phi
                    (TreeSequencePrefix
                      (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc)
                      (↑base.supportPosition : ℕ) base.supportPositive
                      (Nat.le_of_lt_succ base.supportPosition.isLt))
                    base.closure))
                (propext nonempty_prop))) ▸
          base.parallel)),
    nonparallel := id base.nonparallel : HierarchyBase ettB phi };

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHpref320Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
   (generating phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (base : HierarchyBase ett phi)
   (H : TashkinovHierarchy ett base) (B : TreeSequence G e0),
   TreeSequenceInitialSegment B T →
    ∀ (i : Fin H.dividerCount) (hpos : (↑(H.dividerPosition i) : ℕ) ≤ B.length),
     TreeSequencePrefix B (↑(H.dividerPosition i) : ℕ) (H.dividerPositive i) hpos =
      TreeSequencePrefix T (↑(H.dividerPosition i) : ℕ) (H.dividerPositive i) (by omega)

theorem helper_hpref_320.{u_1, u_2} :
    helperHpref320Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett base H B hBT i hpos
  rw [TreeSequencePrefix, TreeSequencePrefix]
  congr
  · funext x
    have hv := hBT.2.1 (Fin.castLE (Nat.succ_le_succ hpos) x)
    simpa using hv.symm
  · funext x
    have heq := hBT.2.2 (Fin.castLE hpos x)
    simpa using heq.symm

end GoldbergSeymour.TerminalHierarchyPrefixPreparation

end
