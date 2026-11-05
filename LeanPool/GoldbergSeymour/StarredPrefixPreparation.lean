/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ElementaryClosedMissingColorOdd
public import LeanPool.GoldbergSeymour.GoodHierarchyElementaryLarge
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast
public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.ParallelClosureUnionElementary
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.PredecessorElementary
public import LeanPool.GoldbergSeymour.TechnicalInductionContext
public import LeanPool.GoldbergSeymour.TechnicalCurrentLadderMissingBoundLarge
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# P2940_T1_Starred Prefix Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_htermMissing_298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = corrU.replacementETT.rounds →
          MaximumProperty current →
            ((∀ (q : Fin current.rounds) (v : V),
                  current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex q.succ = some v →
                      ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                        (j : Fin (current.rounds + (1 : ℕ))),
                        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring (current.series.data.tree q.succ.castSucc)
                                    (TashkinovStoredColors current.series.data q.succ)
                                    (current.series.data.coloring q.succ) sigma →
                                  StableColoringBeforeVertex T' v hvFinal
                                      (TashkinovStoredColors current.series.data j)
                                      (current.series.data.coloring j) sigma ∧
                                    ((0 : ℕ) < (↑j : ℕ) →
                                      StableColoring (current.series.data.tree j.castSucc)
                                        (TashkinovStoredColors current.series.data j)
                                        (current.series.data.coloring j) sigma)) ∧
                ∀ (q r : Fin current.rounds) (vq vr : V),
                  q ≠ r →
                    vq ≠ vr →
                      current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                        current.series.data.kind r.succ = some TashkinovExtensionKind.PE →
                          current.series.data.chosenVertex q.succ = some vq →
                            current.series.data.chosenVertex r.succ = some vr →
                              ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
                                (hvr : vr ∈ TreeSequenceVertexSet T'),
                                ETTFirstAppearanceIndex current vq hvq =
                                    ETTFirstAppearanceIndex current vr hvr →
                                  Disjoint (current.series.data.stored q.succ)
                                    (current.series.data.stored r.succ)) ∧
              (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                let Tterminal : TreeSequence G e0 :=
                  current.series.data.tree terminal.castSucc;
                ∀ (v : V) (gamma delta : Fin k),
                  current.series.data.kind terminal = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex terminal = some v →
                      current.series.data.gamma terminal = some gamma →
                        current.series.data.delta terminal = some delta →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring Tterminal
                                    (TashkinovStoredColors current.series.data terminal)
                                    (current.series.data.coloring terminal) sigma →
                                  ∀ w ∈ TreeSequenceVertexSet Tterminal,
                                    Sum.inl w ∈
                                        TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
                                      w = v) ∧
                (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ∀ (delta : Fin k),
                            DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta →
                              ∀ (v : V),
                                BoundaryColorVertex G sigma
                                    (TreeSequenceVertexSet Tterminal) delta v →
                                  (∃ (w : V),
                                      BoundaryColorVertex G sigma
                                          (TreeSequenceVertexSet Tterminal) delta w ∧
                                        TreeVertexOrder Tterminal w v) →
                                    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                                      (q : Fin current.rounds) (vi : V),
                                      current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.PE ∨
                                          current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.SE →
                                        current.series.data.chosenVertex q.succ = some vi →
                                          ETTFirstAppearanceIndex current v hvFinal ≤
                                              (↑q : ℕ) + (1 : ℕ) →
                                            v = vi ∨ TreeVertexOrder T' v vi) ∧
                  let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ModColoring current sigma) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ)
        (corrU.replacementSeries.data.coloring q.succ) →
    ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE →
    ∀ v ∈ TreeSequenceVertexSet Tn,
    MissingColors G phi v = MissingColors G (ett.series.data.coloring q.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T phi ett U corrU hcurrent q hqterminal Tn htermStable hnonPE v hv
  have hv' : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) := by
    simpa [Tn, hqterminal] using hv
  have hmiss := htermStable.2 v hv'
  have hmissPhi : MissingColors G phi v =
      MissingColors G (ett.series.data.coloring (Fin.last ett.rounds)) v := by
    simpa only [hqterminal, ← corrU.finalGeneratingColoring] using hmiss
  generalize htarget : q.succ = target
  have hstep := ett.series.certified target
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      exact (Fin.succ_ne_zero q htarget).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hcurrent : ett.series.data.coloring (Fin.last ett.rounds) =
          choice.selected := by
        simpa only [hqterminal] using currentColoring
      rw [hcurrent] at hmissPhi
      have hvq : v ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) := by
        simpa [Tn, hqterminal] using hv
      exact hmissPhi.trans (choice.selectedStable.2 v hvq)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hk : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := by
        simpa only [hqterminal] using currentKind
      exact False.elim (hnonPE hk)
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hcurrent : ett.series.data.coloring (Fin.last ett.rounds) =
          ett.series.data.coloring q.castSucc := by
        simpa only [hqterminal] using currentColoring
      rw [hcurrent] at hmissPhi
      exact hmissPhi

private theorem helper_branch_424.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (U : TreeSequence G e0)
      (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet Tn) →
    (ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE →
        ∀ v ∈ TreeSequenceVertexSet Tn,
          MissingColors G phi v = MissingColors G (ett.series.data.coloring q.castSucc) v) →
    ∀ {u : V},
    u ∈ TreeSequenceVertexSet A →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet A →
    u ≠ v →
    H.dividerCount = (0 : ℕ) →
    Disjoint (MissingColors G phi u) (MissingColors G phi v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU hcore H lastH A hkindReplacement
      hUelem q Tn hpreElem htermMissing u hu v hv huv hd
  have hstar : A = baseU.core := by
    dsimp [A, HierarchyStarredStage]
    have hl : lastH = (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [lastH, hd]
    rw [hl]
    rfl
  by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE
  · have hPEU : corrU.replacementETT.series.data.kind
        (Fin.last corrU.replacementETT.rounds) =
          some TashkinovExtensionKind.PE := by
      rw [hkindReplacement]
      exact hPE
    have hcoreU : TreeSequenceInitialSegment baseU.core U := by
      have h := H.coreInsideFirst
      have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [hd]
      rw [hi, H.terminalStage] at h
      exact h
    have hcoreSubset := TreeSequenceInitialSegmentVertexSetSubset hcoreU
    rw [hstar] at hu hv
    exact hUelem (hcoreSubset hu) (hcoreSubset hv) huv
  · have hcoreOrig : base.core = Tn := base.nonparallel hPE
    have hAeq : A = Tn := hstar.trans (hcore.trans hcoreOrig)
    have hmissEq := htermMissing hPE
    rw [hAeq] at hu hv
    have hmu := hmissEq u hu
    have hmv := hmissEq v hv
    simpa only [hmu, hmv] using hpreElem hu hv huv

private theorem helper_branch_456.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    (11 : ℕ) ≤ TashkinovOrder G →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = ett.rounds →
          MaximumProperty current →
            ∀ (base' : HierarchyBase current generating')
              (K : TashkinovHierarchy current base') (_ : GoodHierarchy K),
              let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
              let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating' Tn).card) →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi)
      (H : TashkinovHierarchy corrU.replacementETT baseU) (_ : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
        (0 : ℕ) < lower.rounds →
          lower.rounds < corrU.replacementETT.rounds →
            MaximumProperty lower → (open scoped Classical in LowerRoundProperties lower)) →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = corrU.replacementETT.rounds →
          MaximumProperty current →
            ((∀ (q : Fin current.rounds) (v : V),
                  current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex q.succ = some v →
                      ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                        (j : Fin (current.rounds + (1 : ℕ))),
                        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring (current.series.data.tree q.succ.castSucc)
                                    (TashkinovStoredColors current.series.data q.succ)
                                    (current.series.data.coloring q.succ) sigma →
                                  StableColoringBeforeVertex T' v hvFinal
                                      (TashkinovStoredColors current.series.data j)
                                      (current.series.data.coloring j) sigma ∧
                                    ((0 : ℕ) < (↑j : ℕ) →
                                      StableColoring (current.series.data.tree j.castSucc)
                                        (TashkinovStoredColors current.series.data j)
                                        (current.series.data.coloring j) sigma)) ∧
                ∀ (q r : Fin current.rounds) (vq vr : V),
                  q ≠ r →
                    vq ≠ vr →
                      current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                        current.series.data.kind r.succ = some TashkinovExtensionKind.PE →
                          current.series.data.chosenVertex q.succ = some vq →
                            current.series.data.chosenVertex r.succ = some vr →
                              ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
                                (hvr : vr ∈ TreeSequenceVertexSet T'),
                                ETTFirstAppearanceIndex current vq hvq =
                                    ETTFirstAppearanceIndex current vr hvr →
                                  Disjoint (current.series.data.stored q.succ)
                                    (current.series.data.stored r.succ)) ∧
              (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                let Tterminal : TreeSequence G e0 :=
                  current.series.data.tree terminal.castSucc;
                ∀ (v : V) (gamma delta : Fin k),
                  current.series.data.kind terminal = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex terminal = some v →
                      current.series.data.gamma terminal = some gamma →
                        current.series.data.delta terminal = some delta →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring Tterminal
                                    (TashkinovStoredColors current.series.data terminal)
                                    (current.series.data.coloring terminal) sigma →
                                  ∀ w ∈ TreeSequenceVertexSet Tterminal,
                                    Sum.inl w ∈
                                        TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
                                      w = v) ∧
                (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ∀ (delta : Fin k),
                            DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta →
                              ∀ (v : V),
                                BoundaryColorVertex G sigma
                                    (TreeSequenceVertexSet Tterminal) delta v →
                                  (∃ (w : V),
                                      BoundaryColorVertex G sigma
                                          (TreeSequenceVertexSet Tterminal) delta w ∧
                                        TreeVertexOrder Tterminal w v) →
                                    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                                      (q : Fin current.rounds) (vi : V),
                                      current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.PE ∨
                                          current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.SE →
                                        current.series.data.chosenVertex q.succ = some vi →
                                          ETTFirstAppearanceIndex current v hvFinal ≤
                                              (↑q : ℕ) + (1 : ℕ) →
                                            v = vi ∨ TreeVertexOrder T' v vi) ∧
                  let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ModColoring current sigma) →
    ∀ {u : V},
    u ∈ TreeSequenceVertexSet A →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet A →
    u ≠ v →
    ¬H.dividerCount = (0 : ℕ) →
    Disjoint (MissingColors G phi u) (MissingColors G phi v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hlargeOrder hmissingBound U corrU hMPU baseU H good
      lastH A hlower hcurrent u hu v hv huv hd
  let r : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  have hr : 1 ≤ r.val := by
    dsimp [r]
    have hdpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hd
    omega
  have hstarPositive : A = H.stage r.castSucc := by
    have starPositive : ∀ j : Fin (H.dividerCount + 1), 0 < j.val →
        HierarchyStarredStage H j = H.stage j.castSucc := by
      intro j
      refine Fin.cases ?_ ?_ j
      · intro hj0
        simp at hj0
      · intro i hi
        rfl
    have hs := starPositive r (by omega)
    simpa [A, r] using hs
  obtain ⟨ep, epMP, epRound, epSeries, bp, bpCore, bpClosure,
      bpSupport, HP, hpCount, hpStages, hpDividers, gp, hpData,
      hminusPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 corrU.replacementInput U phi phi
      corrU.replacementETT hMPU baseU H good r hr
  have hlowerP := fun {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating')
      (hpositive : 0 < lower.rounds) (hround : lower.rounds < ep.rounds)
      (hmaximum : MaximumProperty lower) => by
    have hround' : lower.rounds < corrU.replacementETT.rounds := by
      simpa [epRound] using hround
    exact hlower lower hpositive hround' hmaximum
  have hcurrentP := fun {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating')
      (hround : current.rounds = ep.rounds)
      (hmaximum : MaximumProperty current) =>
    hcurrent current (hround.trans epRound) hmaximum
  have hboundP := fun {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating')
      (hround : current.rounds = ep.rounds)
      (hmaximum : MaximumProperty current)
      (bp' : HierarchyBase current generating')
      (K : TashkinovHierarchy current bp') (gK : GoodHierarchy K) => by
    have hround' : current.rounds = ett.rounds :=
      hround.trans (epRound.trans corrU.rungAgreement)
    exact hmissingBound current hround' hmaximum bp' K gK
  have hprefixElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (H.stage r.castSucc)) := by
    exact GoodHierarchyElementaryLarge G k e0 corrU.replacementInput
      (H.stage r.castSucc) phi ep epMP bp HP gp hlowerP hcurrentP
      hlargeOrder hboundP
  have hu' : u ∈ TreeSequenceVertexSet (H.stage r.castSucc) := by
    simpa [hstarPositive] using hu
  have hv' : v ∈ TreeSequenceVertexSet (H.stage r.castSucc) := by
    simpa [hstarPositive] using hv
  exact hprefixElem hu' hv' huv

private theorem helper_helemA_372.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi),
    (11 : ℕ) ≤ TashkinovOrder G →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = ett.rounds →
          MaximumProperty current →
            ∀ (base' : HierarchyBase current generating')
              (K : TashkinovHierarchy current base') (_ : GoodHierarchy K),
              let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
              let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating' Tn).card) →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU) (_ : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
        (0 : ℕ) < lower.rounds →
          lower.rounds < corrU.replacementETT.rounds →
            MaximumProperty lower → (open scoped Classical in LowerRoundProperties lower)) →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = corrU.replacementETT.rounds →
          MaximumProperty current →
            ((∀ (q : Fin current.rounds) (v : V),
                  current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex q.succ = some v →
                      ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                        (j : Fin (current.rounds + (1 : ℕ))),
                        ETTFirstAppearanceIndex current v hvFinal = (↑j : ℕ) + (1 : ℕ) →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring (current.series.data.tree q.succ.castSucc)
                                    (TashkinovStoredColors current.series.data q.succ)
                                    (current.series.data.coloring q.succ) sigma →
                                  StableColoringBeforeVertex T' v hvFinal
                                      (TashkinovStoredColors current.series.data j)
                                      (current.series.data.coloring j) sigma ∧
                                    ((0 : ℕ) < (↑j : ℕ) →
                                      StableColoring (current.series.data.tree j.castSucc)
                                        (TashkinovStoredColors current.series.data j)
                                        (current.series.data.coloring j) sigma)) ∧
                ∀ (q r : Fin current.rounds) (vq vr : V),
                  q ≠ r →
                    vq ≠ vr →
                      current.series.data.kind q.succ = some TashkinovExtensionKind.PE →
                        current.series.data.kind r.succ = some TashkinovExtensionKind.PE →
                          current.series.data.chosenVertex q.succ = some vq →
                            current.series.data.chosenVertex r.succ = some vr →
                              ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
                                (hvr : vr ∈ TreeSequenceVertexSet T'),
                                ETTFirstAppearanceIndex current vq hvq =
                                    ETTFirstAppearanceIndex current vr hvr →
                                  Disjoint (current.series.data.stored q.succ)
                                    (current.series.data.stored r.succ)) ∧
              (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                let Tterminal : TreeSequence G e0 :=
                  current.series.data.tree terminal.castSucc;
                ∀ (v : V) (gamma delta : Fin k),
                  current.series.data.kind terminal = some TashkinovExtensionKind.PE →
                    current.series.data.chosenVertex terminal = some v →
                      current.series.data.gamma terminal = some gamma →
                        current.series.data.delta terminal = some delta →
                          ∀ (sigma : PartialEdgeColoring E k),
                            IsProperEdgeColoring G sigma →
                              IsOneEdgeUncolored sigma e0 →
                                StableColoring Tterminal
                                    (TashkinovStoredColors current.series.data terminal)
                                    (current.series.data.coloring terminal) sigma →
                                  ∀ w ∈ TreeSequenceVertexSet Tterminal,
                                    Sum.inl w ∈
                                        TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
                                      w = v) ∧
                (let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ∀ (delta : Fin k),
                            DefectiveColor G sigma (TreeSequenceVertexSet Tterminal) delta →
                              ∀ (v : V),
                                BoundaryColorVertex G sigma
                                    (TreeSequenceVertexSet Tterminal) delta v →
                                  (∃ (w : V),
                                      BoundaryColorVertex G sigma
                                          (TreeSequenceVertexSet Tterminal) delta w ∧
                                        TreeVertexOrder Tterminal w v) →
                                    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                                      (q : Fin current.rounds) (vi : V),
                                      current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.PE ∨
                                          current.series.data.kind q.succ =
                                            some TashkinovExtensionKind.SE →
                                        current.series.data.chosenVertex q.succ = some vi →
                                          ETTFirstAppearanceIndex current v hvFinal ≤
                                              (↑q : ℕ) + (1 : ℕ) →
                                            v = vi ∨ TreeVertexOrder T' v vi) ∧
                  let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
                  let Tterminal : TreeSequence G e0 :=
                    current.series.data.tree terminal.castSucc;
                  ∀ (sigma : PartialEdgeColoring E k),
                    IsProperEdgeColoring G sigma →
                      IsOneEdgeUncolored sigma e0 →
                        StableColoring Tterminal
                            (TashkinovStoredColors current.series.data terminal)
                            (current.series.data.coloring terminal) sigma →
                          ModColoring current sigma) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet Tn) →
    (ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE →
        ∀ v ∈ TreeSequenceVertexSet Tn,
          MissingColors G phi v = MissingColors G (ett.series.data.coloring q.castSucc) v) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base hlargeOrder hmissingBound U corrU hMPU baseU
      hcore H good lastH A hkindReplacement hlower hcurrent hUelem q Tn hpreElem htermMissing
  unfold ColoredVertexSetElementary
  intro u hu v hv huv
  by_cases hd : H.dividerCount = 0
  · exact @helper_branch_424 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base U corrU baseU hcore H hkindReplacement hUelem hpreElem htermMissing u
      hu v hv huv hd
  · exact @helper_branch_456 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett hlargeOrder hmissingBound U corrU hMPU baseU H good hlower hcurrent u hu v
      hv huv hd
private theorem helper_hAU_497.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (U : TreeSequence G e0)
      (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    (∀ {m n : ℕ} {psi : PartialEdgeColoring E k} (s : TashkinovSeries G k m e0 psi)
        (t : TashkinovSeries G k n e0 psi) (h : m = n),
        s ≍ t →
          ∀ (j : Fin (m + (2 : ℕ))),
            s.data.tree j =
              t.data.tree (Fin.cast (congrArg (fun (a : ℕ) ↦ a + (2 : ℕ)) h) j)) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    let _ : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a,
                Decidable.byContradiction fun (a_1 : ¬a < H.dividerCount + (2 : ℕ)) ↦ by
                  omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d,
                Decidable.byContradiction fun (a_1 : ¬a + d < H.dividerCount + (2 : ℕ)) ↦ by
                  omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    TreeSequenceInitialSegment A U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU hcore H lastH A treeOfSeriesEq q
      hqterminal Tn stageSegment
  by_cases hd : H.dividerCount = 0
  · have hstar : A = baseU.core := by
      dsimp [A, HierarchyStarredStage]
      have hl : lastH = (0 : Fin (H.dividerCount + 1)) := by
        apply Fin.ext
        simp [lastH, hd]
      rw [hl]
      rfl
    by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · have hcoreU : TreeSequenceInitialSegment baseU.core U := by
        have h := H.coreInsideFirst
        have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
            Fin.last (H.dividerCount + 1) := by
          apply Fin.ext
          simp [hd]
        rw [hi, H.terminalStage] at h
        exact h
      simpa [hstar] using hcoreU
    · have hcoreOrig : base.core = Tn := base.nonparallel hPE
      have hAeq : A = Tn := hstar.trans (hcore.trans hcoreOrig)
      have hTnU : TreeSequenceInitialSegment Tn U := by
        have htree := treeOfSeriesEq corrU.replacementETT.series
          corrU.replacementSeries corrU.rungAgreement
          corrU.seriesPresentation
          (Fin.last corrU.replacementETT.rounds).castSucc
        have hidx : Fin.cast (congrArg (fun n => n + 2)
            corrU.rungAgreement)
            ((Fin.last corrU.replacementETT.rounds).castSucc) =
              q.succ.castSucc := by
          apply Fin.ext
          simp [q]
          have hn := ett.roundsPositive
          omega
        rw [hidx] at htree
        have hrepLadder :
            corrU.replacementETT.series.data.tree
              (Fin.last corrU.replacementETT.rounds).castSucc = Tn := by
          calc
            _ = corrU.replacementSeries.data.tree q.succ.castSucc := htree
            _ = ett.series.data.tree q.succ.castSucc := corrU.ladderTreesAgree q
            _ = Tn := by simp [Tn, hqterminal]
        have habove := corrU.replacementETT.abovePenultimate
        have haboveIdx :
            (⟨corrU.replacementETT.rounds, by omega⟩ :
              Fin (corrU.replacementETT.rounds + 2)) =
              (Fin.last corrU.replacementETT.rounds).castSucc := by
          apply Fin.ext
          rfl
        rw [haboveIdx, hrepLadder] at habove
        exact habove
      simpa [hAeq] using hTnU
  · let r : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    have hstarPositive : A = H.stage r.castSucc := by
      have starPositive : ∀ j : Fin (H.dividerCount + 1), 0 < j.val →
          HierarchyStarredStage H j = H.stage j.castSucc := by
        intro j
        refine Fin.cases ?_ ?_ j
        · intro hj
          simp at hj
        · intro i hj
          rfl
      simpa [A, r] using starPositive r (by
        dsimp [r]
        have : 0 < H.dividerCount := Nat.pos_of_ne_zero hd
        exact this)
    have hseg := stageSegment H.dividerCount 1 (by omega)
    have hlast : (⟨H.dividerCount + 1, by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      rfl
    have hseg' : TreeSequenceInitialSegment (H.stage r.castSucc) U := by
      have hridx : r.castSucc = (⟨H.dividerCount, by omega⟩ :
          Fin (H.dividerCount + 2)) := by
        apply Fin.ext
        rfl
      have hend : (⟨H.dividerCount + 1, by omega⟩ :
          Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) := hlast
      have hAstage : H.stage r.castSucc =
          H.stage ⟨H.dividerCount, by omega⟩ := by
        rw [hridx]
      have hUstage : H.stage ⟨H.dividerCount + 1, by omega⟩ = U := by
        rw [hend, H.terminalStage]
      rw [hUstage] at hseg
      simpa [hAstage] using hseg
    simpa [hstarPositive] using hseg'

private theorem helper_hstrictA_584.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (U : TreeSequence G e0)
      (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU),
    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
          base.core.length < U.length) ∧
        (¬ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
          (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length) →
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    let _ : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    A.length < U.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base U corrU baseU hcore H hstrict lastH A Tn
  by_cases hd : H.dividerCount = 0
  · have hstar : A = baseU.core := by
      dsimp [A, HierarchyStarredStage]
      have hl : lastH = (0 : Fin (H.dividerCount + 1)) := by
        apply Fin.ext
        simp [lastH, hd]
      rw [hl]
      rfl
    by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · have h := hstrict.1 hPE
      rw [hstar, hcore]
      exact h
    · have hcoreOrig : base.core = Tn := base.nonparallel hPE
      have hAeq : A = Tn := hstar.trans (hcore.trans hcoreOrig)
      have h := hstrict.2 hPE
      simpa [hAeq] using h
  · let r : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    have hs := H.strict r
    have hstarPositive : A = H.stage r.castSucc := by
      have starPositive : ∀ j : Fin (H.dividerCount + 1), 0 < j.val →
          HierarchyStarredStage H j = H.stage j.castSucc := by
        intro j
        refine Fin.cases ?_ ?_ j
        · intro hj
          simp at hj
        · intro i hj
          rfl
      simpa [A, r] using starPositive r (by
        dsimp [r]
        have : 0 < H.dividerCount := Nat.pos_of_ne_zero hd
        exact this)
    have hend : r.succ = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp [r]
    have hnext : H.stage r.succ = U := by
      rw [hend]
      exact H.terminalStage
    simpa [hstarPositive, hnext] using hs

private theorem helper_branch_733.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    TechnicalInductionContext G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi),
    MaximumDegree G + (1 : ℕ) ≤ k →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU) (_ : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    corrU.replacementETT.series.data.coloring (Fin.last corrU.replacementETT.rounds) = phi →
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) →
    IsProperEdgeColoring G phi →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet Tn) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) →
    H.dividerCount = (0 : ℕ) →
    Odd (TreeSequenceVertexSet A).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx base hdegree U corrU hMPU baseU hcore H good lastH
      A hfinalColor hkindReplacement hproper q hqterminal Tn hpreElem helemA hd
  have hstar : A = baseU.core := by
    dsimp [A, HierarchyStarredStage]
    have hl : lastH = (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [lastH, hd]
    rw [hl]
    rfl
  by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE
  · have hPEU : corrU.replacementETT.series.data.kind
        (Fin.last corrU.replacementETT.rounds) =
          some TashkinovExtensionKind.PE := by
      rw [hkindReplacement]
      exact hPE
    let ctxU : TechnicalInductionContext G k e0
        corrU.replacementETT.rounds :=
      corrU.rungAgreement.symm ▸ ctx
    have hcommon : TreeColorSetClosed G phi baseU.core
        (TreeMissingColors phi
          (corrU.replacementETT.series.data.tree
            (Fin.last corrU.replacementETT.rounds).castSucc) ∩
          TreeMissingColors phi baseU.closure) :=
      ParallelCommonMissingClosed G k e0 corrU.replacementInput U phi phi
        corrU.replacementETT corrU.replacementETT.roundsPositive baseU
        hfinalColor.symm hPEU
        (P2634_T1_PredecessorElementary G k e0 corrU.replacementInput U
          phi corrU.replacementETT ctxU hMPU)
    let Tnu : TreeSequence G e0 :=
      corrU.replacementETT.series.data.tree
        (Fin.last corrU.replacementETT.rounds).castSucc
    let Rzero : Finset (Fin k) :=
      (HierarchyStoredColorsAt H 0).biUnion (good.gamma 0)
    have hfour : 4 ≤
        ((TreeMissingColors phi Tnu ∩ TreeMissingColors phi baseU.closure)
          \ Rzero).card := by
      simpa [Tnu, Rzero] using (good.parallelBase hPEU).2
    obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp (by omega :
      0 < ((TreeMissingColors phi Tnu ∩
        TreeMissingColors phi baseU.closure) \ Rzero).card)
    have hparts := Finset.mem_sdiff.mp halpha
    have hcommonMem := Finset.mem_inter.mp hparts.1
    have hmissingCore : alpha ∈ TreeMissingColors phi baseU.core := by
      unfold TreeMissingColors
      obtain ⟨ou⟩ := (baseU.parallel hPEU).2.2
      rw [ou.vertexSet]
      obtain ⟨v, hv, hmiss⟩ := Finset.mem_biUnion.mp hcommonMem.1
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_union_left _ hv, hmiss⟩
    have hclosedCore := hcommon alpha (Finset.mem_inter.mpr hcommonMem)
    have hmissingA : alpha ∈ TreeMissingColors phi A := by
      simpa [hstar] using hmissingCore
    have hclosedA : TreeColorSetClosed G phi A {alpha} := by
      intro c hc
      have hca : c = alpha := Finset.mem_singleton.mp hc
      subst c
      simpa [hstar] using hclosedCore
    exact ElementaryClosedMissingColorOdd G k e0 phi A alpha
      hproper helemA hmissingA hclosedA
  · have hcoreOrig : base.core = Tn := base.nonparallel hPE
    have hAeq : A = Tn := hstar.trans (hcore.trans hcoreOrig)
    have hprevFacts :
        IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) ∧
        ColoredVertexSetClosed G (ett.series.data.coloring q.castSucc)
          (TreeSequenceVertexSet Tn) := by
      generalize htarget : q.succ = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
          exact (Fin.succ_ne_zero q htarget).elim
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val htarget
            simp at hv
            omega
          subst i
          have htree : ett.series.data.tree q.succ.castSucc = Tn := by
            rw [hqterminal]
          exact ⟨previousProper, by rw [← htree]; exact previousClosed⟩
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper secondStableOneUncolored
          secondStableRelation exitWitness currentColoring currentProper
          currentOneUncolored currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma closedExtension orderedExtension
          strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val htarget
            simp at hv
            omega
          subst i
          have hk : ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.PE := by
            simpa [hqterminal] using currentKind
          exact (hPE hk).elim
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
          have hi : i = q := by
            apply Fin.ext
            have hv := congrArg Fin.val htarget
            simp at hv
            omega
          subst i
          have htree : ett.series.data.tree q.succ.castSucc = Tn := by
            rw [hqterminal]
          exact ⟨previousProper, by rw [← htree]; exact previousClosed⟩
    have hvertex : (TreeSequenceVertexSet Tn).Nonempty := by
      refine ⟨Tn.vertex 0, ?_⟩
      simp [TreeSequenceVertexSet]
    obtain ⟨v, hv⟩ := hvertex
    obtain ⟨alpha, hmiss⟩ :=
      MissingColorsNonemptyOfMaximumDegree G
        (ett.series.data.coloring q.castSucc) hdegree v
    have hclosedAlpha : TreeColorSetClosed G
        (ett.series.data.coloring q.castSucc) Tn {alpha} := by
      intro c hc
      have hca : c = alpha := Finset.mem_singleton.mp hc
      subst c
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      have hfc : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
          (ett.series.data.coloring q.castSucc) f = some alpha := by
        simpa [BoundaryColorEdges] using hf
      exact (hprevFacts.2 hfc.1 hv hfc.2) hmiss
    have hmissTree : alpha ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc) Tn :=
      Finset.mem_biUnion.mpr ⟨v, hv, hmiss⟩
    have hodd := ElementaryClosedMissingColorOdd G k e0
      (ett.series.data.coloring q.castSucc) Tn alpha hprevFacts.1
      hpreElem hmissTree hclosedAlpha
    simpa [hAeq] using hodd

private theorem helper_branch_873.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = ett.rounds →
          MaximumProperty current →
            ∀ (base' : HierarchyBase current generating')
              (K : TashkinovHierarchy current base') (_ : GoodHierarchy K),
              let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
              let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating' Tn).card) →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi)
      (H : TashkinovHierarchy corrU.replacementETT baseU) (_ : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    IsProperEdgeColoring G phi →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) →
    ¬H.dividerCount = (0 : ℕ) →
    Odd (TreeSequenceVertexSet A).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hmissingBound U corrU hMPU baseU H good lastH A
      hproper helemA hd
  let r : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  have hstarPositive : A = H.stage r.castSucc := by
    have starPositive : ∀ j : Fin (H.dividerCount + 1), 0 < j.val →
        HierarchyStarredStage H j = H.stage j.castSucc := by
      intro j
      refine Fin.cases ?_ ?_ j
      · intro hj
        simp at hj
      · intro i hj
        rfl
    simpa [A, r] using starPositive r (by
      dsimp [r]
      have : 0 < H.dividerCount := Nat.pos_of_ne_zero hd
      exact this)
  obtain ⟨ep, epMP, epRound, epSeries, bp, bpCore, bpClosure,
      bpSupport, HP, hpCount, hpStages, hpDividers, gp, hpData,
      hminusPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 corrU.replacementInput U phi phi
      corrU.replacementETT hMPU baseU H good r (by
        dsimp [r]
        omega)
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
  let R : Finset (Fin k) :=
    (HierarchyStoredColorsAt H r).biUnion (good.gamma i.castSucc)
  have hir : i.succ = r := by
    apply Fin.ext
    simp [i, r]
    omega
  have hDsubset : HierarchyStoredColorsAt H r ⊆
      HierarchyStoredColorsAt H i.castSucc := by
    rw [← hir]
    exact HierarchyStoredColorsAntitone H i
  have hDcard : (HierarchyStoredColorsAt H r).card ≤ ett.rounds := by
    have h := HierarchyStoredColorsCardinality H r
    rw [← corrU.rungAgreement]
    exact h
  have hRcard : R.card ≤ 2 * ett.rounds := by
    calc
      R.card ≤ ∑ eta ∈ HierarchyStoredColorsAt H r,
          (good.gamma i.castSucc eta).card := Finset.card_biUnion_le
      _ = 2 * (HierarchyStoredColorsAt H r).card := by
        calc
          (∑ eta ∈ HierarchyStoredColorsAt H r,
              (good.gamma i.castSucc eta).card) =
            ∑ eta ∈ HierarchyStoredColorsAt H r, 2 := by
              apply Finset.sum_congr rfl
              intro eta heta
              exact good.twoColors i.castSucc eta (hDsubset heta)
          _ = 2 * (HierarchyStoredColorsAt H r).card := by
              simp [Nat.mul_comm]
      _ ≤ 2 * ett.rounds := Nat.mul_le_mul_left 2 hDcard
  have hlargeL := hmissingBound ep
    (epRound.trans corrU.rungAgreement) epMP bp HP gp
  have hprefixSegment : TreeSequenceInitialSegment
      (ep.series.data.tree (Fin.last ep.rounds).castSucc) A := by
    have hidx : (Fin.last ep.rounds).castSucc =
        (⟨ep.rounds, by omega⟩ : Fin (ep.rounds + 2)) := by
      apply Fin.ext
      rfl
    rw [hidx, hstarPositive]
    exact ep.abovePenultimate
  have hmissSubset :
      TreeMissingColors phi
          (ep.series.data.tree (Fin.last ep.rounds).castSucc) ⊆
        TreeMissingColors phi A := by
    intro c hc
    unfold TreeMissingColors at hc ⊢
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hprefixSegment hv, hcv⟩
  have hlargeA : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi A).card := by
    have hlargeL' : 2 * ett.rounds + 11 ≤
        (TreeMissingColors phi
          (ep.series.data.tree (Fin.last ep.rounds).castSucc)).card := by
      rw [← corrU.rungAgreement, ← epRound]
      exact hlargeL
    exact le_trans hlargeL' (Finset.card_le_card hmissSubset)
  have hInter :
      (TreeMissingColors phi A ∩ R).card ≤ R.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hInterBound : (TreeMissingColors phi A ∩ R).card ≤
      2 * ett.rounds := le_trans hInter hRcard
  have hInterBound' : (R ∩ TreeMissingColors phi A).card ≤
      2 * ett.rounds := by
    simpa [Finset.inter_comm] using hInterBound
  have hdiff : 11 ≤ (TreeMissingColors phi A \ R).card := by
    rw [Finset.card_sdiff]
    omega
  obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp (by omega :
    0 < (TreeMissingColors phi A \ R).card)
  have hmissingA : alpha ∈ TreeMissingColors phi A :=
    (Finset.mem_sdiff.mp halpha).1
  have hiGamma : (⟨r.val - 1, by omega⟩ : Fin (H.dividerCount + 1)) =
      i.castSucc := by
    apply Fin.ext
    simp [r, i]
  have hminusA : TreeColorSetMinusClosed G phi A R := by
    simpa [R, hstarPositive, hiGamma] using hminusPrefix
  have hclosedAlpha : TreeColorSetClosed G phi A {alpha} := by
    intro c hc
    have hca : c = alpha := Finset.mem_singleton.mp hc
    subst c
    exact hminusA alpha halpha
  exact ElementaryClosedMissingColorOdd G k e0 phi A alpha
    hproper helemA hmissingA hclosedAlpha

private theorem helper_hoddA_624.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    TechnicalInductionContext G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi),
    MaximumDegree G + (1 : ℕ) ≤ k →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = ett.rounds →
          MaximumProperty current →
            ∀ (base' : HierarchyBase current generating')
              (K : TashkinovHierarchy current base') (_ : GoodHierarchy K),
              let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
              let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating' Tn).card) →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU) (_ : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    corrU.replacementETT.series.data.coloring (Fin.last corrU.replacementETT.rounds) = phi →
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) →
    IsProperEdgeColoring G phi →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have hn : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet Tn) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) →
    Odd (TreeSequenceVertexSet A).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx base hdegree hmissingBound U corrU hMPU baseU
      hcore H good lastH A hfinalColor hkindReplacement hproper q hqterminal Tn hpreElem helemA
  by_cases hd : H.dividerCount = 0
  · exact @helper_branch_733 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett ctx base hdegree U corrU hMPU baseU hcore H good hfinalColor
      hkindReplacement hproper hqterminal hpreElem helemA hd
  · exact @helper_branch_873 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett hmissingBound U corrU hMPU baseU H good hproper helemA hd
private theorem helper_hkindReplacement_1362.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    (∀ {m n : ℕ} {psi : PartialEdgeColoring E k} (s : TashkinovSeries G k m e0 psi)
        (t : TashkinovSeries G k n e0 psi) (h : m = n),
        s ≍ t →
          ∀ (j : Fin (m + (1 : ℕ))),
            s.data.kind j = t.data.kind (Fin.cast (congrArg Nat.succ h) j)) →
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
      ett.series.data.kind (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett U corrU kindOfSeriesEq
  calc
    corrU.replacementETT.series.data.kind
        (Fin.last corrU.replacementETT.rounds) =
      corrU.replacementSeries.data.kind (Fin.last ett.rounds) :=
        kindOfSeriesEq corrU.replacementETT.series corrU.replacementSeries
          corrU.rungAgreement corrU.seriesPresentation
          (Fin.last corrU.replacementETT.rounds) |>.trans (by
            congr 1
            apply Fin.ext
            simp)
    _ = ett.series.data.kind (Fin.last ett.rounds) :=
      corrU.extensionKindsAgree (Fin.last ett.rounds)

private theorem helper_stageSegment_1552.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corrU.replacementETT phi)
      (H : TashkinovHierarchy corrU.replacementETT baseU),
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = corrU.replacementETT.rounds →
          MaximumProperty current →
            ∀ (x : HierarchyBase current generating') (x_1 : TashkinovHierarchy current x)
              (_ : GoodHierarchy x_1),
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating'
                    (current.series.data.tree (Fin.last current.rounds).castSucc)).card) →
    (∀ (X : TreeSequence G e0), TreeSequenceInitialSegment X X) →
    (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment
      (H.stage
        (⟨a,
            Decidable.byContradiction fun (a_1 : ¬a < H.dividerCount + (2 : ℕ)) ↦ by
              omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))))
      (H.stage
        (⟨a + d,
            Decidable.byContradiction fun (a_1 : ¬a + d < H.dividerCount + (2 : ℕ)) ↦ by
              omega⟩ :
          Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U corrU baseU H hbound segmentRefl segmentTrans a d
  induction d with
  | zero =>
      intro hbound
      simpa using segmentRefl (H.stage ⟨a, by omega⟩)
  | succ d ih =>
      intro hbound
      have hprev := ih (by omega)
      have hnext := H.nested ⟨a + d, by omega⟩
      have hnext' : TreeSequenceInitialSegment
          (H.stage ⟨a + d, by omega⟩)
          (H.stage ⟨a + (d + 1), by omega⟩) := by
        simpa [Nat.add_assoc] using hnext
      exact segmentTrans hprev hnext'

private theorem helper_hRplus_1583.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corrU.replacementETT phi)
      (H : TashkinovHierarchy corrU.replacementETT baseU) (good : GoodHierarchy H),
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Dplus : Finset (Fin k) := HierarchyTerminalStoredColors H;
    Dplus ⊆ HierarchyStoredColorsAt H lastH →
    (HierarchyStoredColorsAt H lastH).card ≤ ett.rounds →
    let Rplus : Finset (Fin k) := Dplus.biUnion (good.gamma lastH);
    Rplus.card ≤ (2 : ℕ) * ett.rounds := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett U corrU baseU H good lastH Dplus hDsubset hDcard Rplus
  calc
    Rplus.card ≤ ∑ eta ∈ Dplus, (good.gamma lastH eta).card :=
      Finset.card_biUnion_le
    _ = 2 * Dplus.card := by
      calc
        (∑ eta ∈ Dplus, (good.gamma lastH eta).card) =
            ∑ eta ∈ Dplus, 2 := by
          apply Finset.sum_congr rfl
          intro eta heta
          exact good.twoColors lastH eta (hDsubset heta)
        _ = 2 * Dplus.card := by simp [Nat.mul_comm]
    _ ≤ 2 * ett.rounds := Nat.mul_le_mul_left 2
      (le_trans (Finset.card_le_card hDsubset) hDcard)

private theorem helper_continuation_1569.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    TechnicalInductionContext G k e0 ett.rounds →
    MaximumProperty ett →
    ∀ (base : HierarchyBase ett phi),
    MaximumDegree G + (1 : ℕ) ≤ k →
    (11 : ℕ) ≤ TashkinovOrder G →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (current : ExtendedTashkinovTree G k e0 input' T' generating'),
        current.rounds = ett.rounds →
          MaximumProperty current →
            ∀ (base' : HierarchyBase current generating')
              (K : TashkinovHierarchy current base') (_ : GoodHierarchy K),
              let n : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
              let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc;
              (2 : ℕ) * current.rounds + (11 : ℕ) ≤
                (TreeMissingColors generating' Tn).card) →
    ∀ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
    MaximumProperty corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi),
    baseU.core = base.core →
    ∀ (H : TashkinovHierarchy corrU.replacementETT baseU) (good : GoodHierarchy H),
    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
          base.core.length < U.length) ∧
        (¬ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
          (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length) →
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let _ : TreeSequence G e0 := HierarchyStarredStage H lastH;
    let _ : Finset (Fin k) := HierarchyTerminalStoredColors H;
    (∀ {m n : ℕ} {psi : PartialEdgeColoring E k} (s : TashkinovSeries G k m e0 psi)
        (t : TashkinovSeries G k n e0 psi) (h : m = n),
        s ≍ t →
          ∀ (j : Fin (m + (2 : ℕ))),
            s.data.tree j =
              t.data.tree (Fin.cast (congrArg (fun (a : ℕ) ↦ a + (2 : ℕ)) h) j)) →
    corrU.replacementETT.series.data.coloring (Fin.last corrU.replacementETT.rounds) = phi →
    corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
        (0 : ℕ) < lower.rounds →
          lower.rounds < corrU.replacementETT.rounds →
            MaximumProperty lower → (open scoped Classical in LowerRoundProperties lower)) →
    let lastH : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H lastH;
    IsProperEdgeColoring G phi ∧
      IsOneEdgeUncolored phi e0 ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) ∧
          ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) ∧
            TreeSequenceInitialSegment A U ∧
              A.length < U.length ∧
                Odd (TreeSequenceVertexSet A).card ∧
                  ((HierarchyTerminalStoredColors H).biUnion (good.gamma lastH)).card <
                    (TreeMissingColors phi U).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP base hdegree hlargeOrder hmissingBound U corrU
      hMPU baseU hcore H good hstrict lastH A Dplus treeOfSeriesEq hfinalColor hkindReplacement
      hproper hone hlower
  have hcurrent := fun {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating')
      (hround : current.rounds = corrU.replacementETT.rounds)
      (hmaximum : MaximumProperty current) =>
    And.intro
      (ctx.currentThree current (hround.trans corrU.rungAgreement) hmaximum)
      (And.intro
        (ctx.currentFour current (hround.trans corrU.rungAgreement) hmaximum)
        (And.intro
          (ctx.currentFive current (hround.trans corrU.rungAgreement) hmaximum)
          (ctx.currentSix current (hround.trans corrU.rungAgreement) hmaximum)))
  have hbound := fun {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating')
      (hround : current.rounds = corrU.replacementETT.rounds)
      (hmaximum : MaximumProperty current)
      (_ : HierarchyBase current generating')
      (_ : TashkinovHierarchy current ‹HierarchyBase current generating'›)
      (_ : GoodHierarchy ‹TashkinovHierarchy current
        ‹HierarchyBase current generating'››) => by
    have hround' : current.rounds = ett.rounds := hround.trans corrU.rungAgreement
    let currentCtx : TechnicalInductionContext G k e0 current.rounds :=
      hround'.symm ▸ ctx
    exact TechnicalCurrentLadderMissingBoundLarge G k e0 input' T'
      generating' current hmaximum currentCtx hdegree hlargeOrder
  have hUelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) :=
    GoodHierarchyElementaryLarge G k e0 corrU.replacementInput U phi
      corrU.replacementETT hMPU baseU H good hlower hcurrent hlargeOrder hbound
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by
    have hn := ett.roundsPositive
    omega⟩
  have hqterminal : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    have hn := ett.roundsPositive
    omega
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree (Fin.last ett.rounds).castSucc
  have hpreElem : ColoredVertexSetElementary G
      (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet Tn) := by
    intro u hu v hv huv
    exact P2634_T1_PredecessorElementary G k e0 input T phi ett ctx hMP
      (u := u) hu hv huv
  have htermStable := corrU.replacementStable q
  have htermMissing := @helper_htermMissing_298 V E inferInstance inferInstance inferInstance G k e0
      input T phi ett U corrU hcurrent hqterminal htermStable
  have helemA := @helper_helemA_372 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base hlargeOrder hmissingBound U corrU hMPU baseU hcore H good
      hkindReplacement hlower hcurrent hUelem hpreElem htermMissing
  have segmentRefl (X : TreeSequence G e0) : TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, hvxy, hexy⟩
    rcases hYZ with ⟨hyz, hvyz, heyz⟩
    refine ⟨le_trans hxy hyz, ?_, ?_⟩
    · intro i
      have hmid := hvyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      simpa using hmid.trans (hvxy i)
    · intro i
      have hmid := heyz (Fin.castLE hxy i)
      simpa using hmid.trans (hexy i)
  have stageSegment := @helper_stageSegment_1552 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett U corrU baseU H hbound segmentRefl segmentTrans
  have hAU := @helper_hAU_497 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base U corrU baseU hcore H treeOfSeriesEq hqterminal stageSegment
  have hstrictA := @helper_hstrictA_584 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base U corrU baseU hcore H hstrict
  have hoddA := @helper_hoddA_624 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett ctx base hdegree hmissingBound U corrU hMPU baseU hcore H good hfinalColor
      hkindReplacement hproper hqterminal hpreElem helemA
  have hDsubset : Dplus ⊆ HierarchyStoredColorsAt H lastH :=
    (HierarchyTerminalStoredColorsSubsetLast H).1
  have hDcard : (HierarchyStoredColorsAt H lastH).card ≤ ett.rounds := by
    have h := HierarchyStoredColorsCardinality H lastH
    rw [← corrU.rungAgreement]
    exact h
  let Rplus : Finset (Fin k) := Dplus.biUnion (good.gamma lastH)
  have hRplus := @helper_hRplus_1583 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett U corrU baseU H good hDsubset hDcard
  have hlargeFinal := hmissingBound corrU.replacementETT
    corrU.rungAgreement hMPU baseU H good
  have hlastIntoU : TreeSequenceInitialSegment
      (corrU.replacementETT.series.data.tree
        (Fin.last corrU.replacementETT.rounds).castSucc) U :=
    corrU.replacementETT.abovePenultimate
  have hmissingIntoU : TreeMissingColors phi
      (corrU.replacementETT.series.data.tree
        (Fin.last corrU.replacementETT.rounds).castSucc) ⊆
      TreeMissingColors phi U := by
    intro c hc
    unfold TreeMissingColors at hc ⊢
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hlastIntoU hv, hcv⟩
  have hlargeU : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi U).card := by
    have hlargeFinal' : 2 * ett.rounds + 11 ≤
        (TreeMissingColors phi
          (corrU.replacementETT.series.data.tree
            (Fin.last corrU.replacementETT.rounds).castSucc)).card := by
      rw [← corrU.rungAgreement]
      exact hlargeFinal
    exact le_trans hlargeFinal' (Finset.card_le_card hmissingIntoU)
  refine ⟨hproper, hone, helemA, hUelem, hAU, hstrictA, hoddA, ?_⟩
  calc
    (Dplus.biUnion (good.gamma lastH)).card ≤ 2 * ett.rounds := by
      simpa [Rplus] using hRplus
    _ < (TreeMissingColors phi U).card := by omega

theorem P2940_T1_StarredPrefixPreparation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlargeOrder : 11 <= TashkinovOrder G)
    (hmissingBound : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = ett.rounds -> MaximumProperty current ->
      forall (base' : HierarchyBase current generating')
        (K : TashkinovHierarchy current base'), GoodHierarchy K ->
        let n : Fin (current.rounds + 1) := Fin.last current.rounds
        let Tn := current.series.data.tree n.castSucc
        2 * current.rounds + 11 <= (TreeMissingColors generating' Tn).card)
    (U : TreeSequence G e0)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (hMPU : MaximumProperty corrU.replacementETT)
    (baseU : HierarchyBase corrU.replacementETT phi)
    (hcore : baseU.core = base.core)
    (H : TashkinovHierarchy corrU.replacementETT baseU)
    (good : GoodHierarchy H)
    (hstrict :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE -> base.core.length < U.length) /\
      (Not (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE) ->
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length)) :
    let lastH : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H lastH
    IsProperEdgeColoring G phi /\ IsOneEdgeUncolored phi e0 /\
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) /\
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet U) /\
    TreeSequenceInitialSegment A U /\ A.length < U.length /\
    Odd (TreeSequenceVertexSet A).card /\
    ((HierarchyTerminalStoredColors H).biUnion (good.gamma lastH)).card <
      (TreeMissingColors phi U).card := by
  classical
  let lastH : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A : TreeSequence G e0 := HierarchyStarredStage H lastH
  let Dplus := HierarchyTerminalStoredColors H
  have treeOfSeriesEq {m n : ℕ} {psi : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 psi)
      (t : TashkinovSeries G k n e0 psi)
      (h : m = n) (hs : HEq s t) (j : Fin (m + 2)) :
      s.data.tree j = t.data.tree (Fin.cast (congrArg (fun a => a + 2) h) j) := by
    cases h
    cases hs
    rfl
  have coloringOfSeriesEq {m n : ℕ} {psi : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 psi)
      (t : TashkinovSeries G k n e0 psi)
      (h : m = n) (hs : HEq s t) (j : Fin (m + 1)) :
      s.data.coloring j = t.data.coloring (Fin.cast (congrArg Nat.succ h) j) := by
    cases h
    cases hs
    rfl
  have kindOfSeriesEq {m n : ℕ} {psi : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 psi)
      (t : TashkinovSeries G k n e0 psi)
      (h : m = n) (hs : HEq s t) (j : Fin (m + 1)) :
      s.data.kind j = t.data.kind (Fin.cast (congrArg Nat.succ h) j) := by
    cases h
    cases hs
    rfl
  have hfinalColor :
      corrU.replacementETT.series.data.coloring
          (Fin.last corrU.replacementETT.rounds) = phi := by
    have hc := coloringOfSeriesEq corrU.replacementETT.series
      corrU.replacementSeries corrU.rungAgreement corrU.seriesPresentation
      (Fin.last corrU.replacementETT.rounds)
    have hi : Fin.cast (congrArg Nat.succ corrU.rungAgreement)
        (Fin.last corrU.replacementETT.rounds) = Fin.last ett.rounds := by
      apply Fin.ext
      simp
    rw [hi] at hc
    exact hc.trans corrU.finalGeneratingColoring.symm
  have hcolorOriginal :
      corrU.replacementETT.series.data.coloring
          (Fin.last corrU.replacementETT.rounds) =
        corrU.replacementSeries.data.coloring (Fin.last ett.rounds) := by
    exact coloringOfSeriesEq corrU.replacementETT.series
      corrU.replacementSeries corrU.rungAgreement corrU.seriesPresentation
      (Fin.last corrU.replacementETT.rounds) |>.trans (by
        congr 1
        apply Fin.ext
        simp)
  have hkindReplacement := @helper_hkindReplacement_1362 V E inferInstance inferInstance
      inferInstance G k e0 input T phi ett U corrU kindOfSeriesEq
  have hproper : IsProperEdgeColoring G phi := by
    rw [← hfinalColor]
    rw [hcolorOriginal]
    exact corrU.replacementProper (Fin.last ett.rounds)
  have hone : IsOneEdgeUncolored phi e0 := by
    rw [← hfinalColor]
    rw [hcolorOriginal]
    exact corrU.replacementOneUncolored (Fin.last ett.rounds)
  have hlower : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < corrU.replacementETT.rounds ->
      MaximumProperty lower ->
      ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext := lower.series.data.tree (Fin.last (lower.rounds + 1))
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tnext (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           forall alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) ->
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((forall (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
          lower.series.data.chosenVertex q.succ = some v ->
          forall hvFinal : v ∈ TreeSequenceVertexSet T',
          forall j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 ->
            forall sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
              StableColoring (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma ->
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val -> StableColoring (lower.series.data.tree j.castSucc)
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma)) ∧
          forall (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r -> vq ≠ vr ->
            lower.series.data.kind q.succ = some TashkinovExtensionKind.PE ->
            lower.series.data.kind r.succ = some TashkinovExtensionKind.PE ->
            lower.series.data.chosenVertex q.succ = some vq ->
            lower.series.data.chosenVertex r.succ = some vr ->
            forall (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                ETTFirstAppearanceIndex lower vr hvr ->
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         forall (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE ->
           lower.series.data.chosenVertex n = some v ->
           lower.series.data.gamma n = some gamma ->
           lower.series.data.delta n = some delta ->
           forall sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
             StableColoring Tn (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma ->
             forall w, w ∈ TreeSequenceVertexSet Tn ->
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
                 w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           forall delta : Fin k,
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta ->
             forall v : V,
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v ->
               (exists w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn w v) ->
               forall (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                     some TashkinovExtensionKind.PE ∨
                   lower.series.data.kind q.succ =
                     some TashkinovExtensionKind.SE) ->
                 lower.series.data.chosenVertex q.succ = some vi ->
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 ->
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn := lower.series.data.tree n.castSucc
         forall sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
           StableColoring Tn (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma ->
           ModColoring lower sigma) := by
    intro input' T' generating' lower hpositive hround hmaximum
    have hround' : lower.rounds < ett.rounds := by
      simpa [corrU.rungAgreement] using hround
    exact ⟨ctx.lowerOne lower hpositive hround' hmaximum,
      ctx.lowerTwo lower hpositive hround' hmaximum,
      ctx.lowerThree lower hpositive hround' hmaximum,
      ctx.lowerFour lower hpositive hround' hmaximum,
      ctx.lowerFive lower hpositive hround' hmaximum,
      ctx.lowerSix lower hpositive hround' hmaximum⟩
  exact @helper_continuation_1569 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett ctx hMP base hdegree hlargeOrder hmissingBound U corrU hMPU baseU hcore
      H good hstrict treeOfSeriesEq hfinalColor hkindReplacement hproper hone hlower
end GoldbergSeymour

end
