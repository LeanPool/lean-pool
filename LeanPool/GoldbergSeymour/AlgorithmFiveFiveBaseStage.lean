/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AlgorithmFiveFiveInitialGoodHierarchy
public import LeanPool.GoldbergSeymour.AlgorithmFiveFiveParallelStrictGrowth

public import LeanPool.GoldbergSeymour.GoodHierarchyRestrictedAugmentation

/-!
# Algorithm Five Five Base Stage

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem AlgorithmFiveFiveBaseStage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hmod : ModColoring ett phi)
    (base : HierarchyBase ett phi)
    (hcoreStrict :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          base.core.length)
    (hcoreClosure :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        TashkinovClosure phi base.core
          (ett.series.data.tree (Fin.last (ett.rounds + 1))))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hparallelFacts :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (∃ alpha : Fin k,
          alpha ∈ TreeMissingColors phi base.core ∧
            ¬ TreeColorSetClosed G phi base.core {alpha}) ∧
        TreeColorSetClosed G phi base.core
          (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure) ∧
        4 ≤ (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure).card) :
    ∃ (J U : TreeSequence G e0)
        (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
      (((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE ∧ J = base.core) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J)) ∧
      TashkinovAugmentationSequence phi J U ∧
      TreeSequenceInitialSegment J U ∧
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE → base.core.length < U.length) ∧
      (ett.series.data.kind (Fin.last ett.rounds) ≠
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < U.length) ∧
      MaximumProperty corrU.replacementETT ∧
      ∃ baseU : HierarchyBase corrU.replacementETT phi,
        baseU.core = base.core ∧
        baseU.closure = base.closure ∧
        baseU.supportPosition.val = base.supportPosition.val ∧
        ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
          KU.dividerCount = 0 ∧
          KU.stage 0 =
            ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
          KU.stage (Fin.last (KU.dividerCount + 1)) = U ∧
          ∃ goodU : GoodHierarchy KU, (
            (∀ eta : Fin k,
              eta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) →
                (goodU.gamma (Fin.last KU.dividerCount) eta).card = 2 ∧
                goodU.gamma (Fin.last KU.dividerCount) eta ⊆
                  TreeMissingColors phi
                      (ett.series.data.tree
                        (Fin.last ett.rounds).castSucc) \
                    HierarchySegmentColors KU
                      (Fin.last KU.dividerCount) eta) ∧
            (∀ eta theta : Fin k,
              eta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) →
              theta ∈ HierarchyStoredColorsAt KU
                  (Fin.last KU.dividerCount) → eta ≠ theta →
                Disjoint
                  (goodU.gamma (Fin.last KU.dividerCount) eta)
                  (goodU.gamma (Fin.last KU.dividerCount) theta)) ∧
            (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE →
              ¬ TreeColorSetMinusClosed G phi base.core
                ((HierarchyStoredColorsAt KU
                    (Fin.last KU.dividerCount)).biUnion
                  (goodU.gamma (Fin.last KU.dividerCount))) ∧
              4 ≤ ((TreeMissingColors phi
                    (ett.series.data.tree
                      (Fin.last ett.rounds).castSucc) ∩
                  TreeMissingColors phi base.closure) \
                (HierarchyStoredColorsAt KU
                    (Fin.last KU.dividerCount)).biUnion
                  (goodU.gamma (Fin.last KU.dividerCount))).card)) ∧
            TreeColorSetMinusClosed G phi U
              ((HierarchyTerminalStoredColors KU).biUnion
                (goodU.gamma (Fin.last KU.dividerCount)))) := by
  classical
  obtain ⟨J, corrJ, hMPJ, hJfinal, baseJ, hcoreJ, hclosureJ, hsupportJ,
      KJ, hzeroJ, hstageZeroJ, hstageTerminalJ, hseedFull⟩ :=
    AlgorithmFiveFiveSeed G k e0 input T phi ett hMP base hcoreStrict
      hcoreClosure
  have hseed :
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE ∧ J = base.core) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J)) := by
    rcases hseedFull with hparallel | hnonparallel
    · exact Or.inl hparallel
    · rcases hnonparallel with ⟨hkind, f, hf, hadjoin, hroute⟩
      exact Or.inr ⟨hkind, f, hf, hadjoin⟩
  obtain ⟨goodJ, hmissingJ, hparallelJ⟩ :=
    AlgorithmFiveFiveInitialGoodHierarchy G k e0 input T phi ett base J corrJ
      baseJ KJ hcoreJ hclosureJ hzeroJ hstageZeroJ hseed hlarge
      hparallelFacts
  obtain ⟨m, chain, U, hfirst, hlast, hsteps, hlengths, hsegments,
      hvertices, hsequence, havoid, hmaximal, corrU, hMPU, baseU, hcoreU,
      hclosureU, hsupportU, KU, hcount, hstages, hdividers, goodU, hgamma,
      hstored, hminus⟩ :=
    GoodHierarchyRestrictedAugmentation G k e0 input T phi phi ett hmod hMP
      J corrJ baseJ KJ goodJ
  have hJU : TreeSequenceInitialSegment J U := by
    have h := hsegments (0 : Fin (m + 1)) (Fin.last m) (by simp)
    rw [hfirst, hlast] at h
    exact h
  have hUlength : U.length = J.length + m := by
    calc
      U.length = (chain (Fin.last m)).length := by rw [hlast]
      _ = J.length + (Fin.last m).val := hlengths (Fin.last m)
      _ = J.length + m := by simp
  have hzeroEndpoint : m = 0 → U = J := by
    intro hm
    subst m
    calc
      U = chain (Fin.last 0) := hlast.symm
      _ = chain 0 := by congr
      _ = J := hfirst
  have hstrictPE :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        base.core.length < U.length := by
    intro hPE
    have hJcore : J = base.core := by
      rcases hseed with hparallel | hnonparallel
      · exact hparallel.2
      · rcases hnonparallel.1 with hSE | hRE
        · rw [hPE] at hSE
          simp at hSE
        · rw [hPE] at hRE
          simp at hRE
    have hJcoreJ : J = baseJ.core := hJcore.trans hcoreJ.symm
    have hgrowth := AlgorithmFiveFiveParallelStrictGrowth G k e0 input T phi
      phi ett J corrJ baseJ KJ goodJ hzeroJ hPE hJcoreJ m U hUlength
      hzeroEndpoint hmaximal
    rwa [hJcore] at hgrowth
  have hstrictNonPE :
      ett.series.data.kind (Fin.last ett.rounds) ≠
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          U.length := by
    intro hnonPE
    rcases hseed with hparallel | hnonparallel
    · exact (hnonPE hparallel.1).elim
    · rcases hnonparallel with ⟨hkind, f, hf, hadjoin⟩
      rcases hadjoin with ⟨hlen, hinitial, hedge⟩
      omega
  have hzeroU : KU.dividerCount = 0 := by omega
  let lastU : Fin (KU.dividerCount + 1) := Fin.last KU.dividerCount
  let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
  let oldIndex : Fin (KJ.dividerCount + 1) :=
    Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) lastU
  have holdLast : oldIndex = lastJ := by
    apply Fin.ext
    simp [oldIndex, lastU, lastJ]
  have htransport := hstages lastU
  dsimp only at htransport
  have hstageTransport : KU.stage lastU.castSucc = KJ.stage lastJ.castSucc := by
    simpa [oldIndex, holdLast] using htransport.1
  have hstoredTransport : HierarchyStoredColorsAt KU lastU =
      HierarchyStoredColorsAt KJ lastJ := by
    simpa [oldIndex, holdLast] using htransport.2.2.1
  have hmissingTransport : HierarchyStageMissingColors KU lastU =
      HierarchyStageMissingColors KJ lastJ := by
    simpa [oldIndex, holdLast] using htransport.2.2.2
  have hgammaTransport : ∀ eta : Fin k,
      goodU.gamma lastU eta = goodJ.gamma lastJ eta := by
    intro eta
    simpa [oldIndex, holdLast] using hgamma lastU eta
  have hmissingU : HierarchyStageMissingColors KU lastU =
      TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
    exact hmissingTransport.trans hmissingJ
  have hunionTransport :
      (HierarchyStoredColorsAt KU lastU).biUnion (goodU.gamma lastU) =
        (HierarchyStoredColorsAt KJ lastJ).biUnion (goodJ.gamma lastJ) := by
    apply Finset.ext
    intro c
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨eta, heta, hc⟩
      refine ⟨eta, ?_, ?_⟩
      · rwa [← hstoredTransport]
      · rwa [← hgammaTransport eta]
    · rintro ⟨eta, heta, hc⟩
      refine ⟨eta, ?_, ?_⟩
      · rwa [hstoredTransport]
      · rwa [hgammaTransport eta]
  have hstageZeroU : KU.stage 0 =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    have hzeroOld :
        Fin.cast (congrArg (fun n : ℕ => n + 1) hcount)
            (0 : Fin (KU.dividerCount + 1)) =
          (0 : Fin (KJ.dividerCount + 1)) := by
      apply Fin.ext
      rfl
    have hs := (hstages (0 : Fin (KU.dividerCount + 1))).1
    rw [hzeroOld] at hs
    calc
      KU.stage 0 = KU.stage (0 : Fin (KU.dividerCount + 1)).castSucc := by
        congr 1
      _ = KJ.stage (0 : Fin (KJ.dividerCount + 1)).castSucc := hs
      _ = KJ.stage 0 := by congr 1
      _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hstageZeroJ
  have hpairData :
      (∀ eta : Fin k,
        eta ∈ HierarchyStoredColorsAt KU lastU →
          (goodU.gamma lastU eta).card = 2 ∧
          goodU.gamma lastU eta ⊆
            TreeMissingColors phi
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) \
              HierarchySegmentColors KU lastU eta) := by
    intro eta heta
    refine ⟨goodU.twoColors lastU eta heta, ?_⟩
    have ha := goodU.avoidance lastU eta heta
    rwa [hmissingU] at ha
  have hdisjointData :
    ∀ eta theta : Fin k, eta ∈ HierarchyStoredColorsAt KU lastU → theta ∈ HierarchyStoredColorsAt
        KU lastU → eta ≠ theta → Disjoint (goodU.gamma lastU eta) (goodU.gamma lastU theta) := by
    intro eta theta heta htheta hne
    exact goodU.disjointPairs lastU eta theta heta htheta hne
  have hparallelData :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        ¬ TreeColorSetMinusClosed G phi base.core
            ((HierarchyStoredColorsAt KU lastU).biUnion
              (goodU.gamma lastU)) ∧
        4 ≤ ((TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure) \
          (HierarchyStoredColorsAt KU lastU).biUnion
            (goodU.gamma lastU)).card := by
    intro hPE
    have hp := hparallelJ hPE
    rwa [hunionTransport]
  refine ⟨J, U, corrU, hseed, hsequence, hJU, hstrictPE, hstrictNonPE,
    hMPU, baseU, ?_, ?_, ?_, KU, hzeroU, hstageZeroU, KU.terminalStage,
    goodU, ?_⟩
  · exact hcoreU.trans hcoreJ
  · exact hclosureU.trans hclosureJ
  · exact hsupportU.trans hsupportJ
  · change
      ((∀ eta : Fin k,
          eta ∈ HierarchyStoredColorsAt KU lastU →
            (goodU.gamma lastU eta).card = 2 ∧
            goodU.gamma lastU eta ⊆
              TreeMissingColors phi
                  (ett.series.data.tree (Fin.last ett.rounds).castSucc) \
                HierarchySegmentColors KU lastU eta) ∧
        (∀ eta theta : Fin k,
          eta ∈ HierarchyStoredColorsAt KU lastU →
          theta ∈ HierarchyStoredColorsAt KU lastU → eta ≠ theta →
            Disjoint (goodU.gamma lastU eta) (goodU.gamma lastU theta)) ∧
        (ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE →
          ¬ TreeColorSetMinusClosed G phi base.core
              ((HierarchyStoredColorsAt KU lastU).biUnion
                (goodU.gamma lastU)) ∧
          4 ≤ ((TreeMissingColors phi
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
              TreeMissingColors phi base.closure) \
            (HierarchyStoredColorsAt KU lastU).biUnion
              (goodU.gamma lastU)).card)) ∧
        TreeColorSetMinusClosed G phi U
          ((HierarchyTerminalStoredColors KU).biUnion
            (goodU.gamma lastU))
    exact ⟨⟨hpairData, hdisjointData, hparallelData⟩, hminus⟩

end GoldbergSeymour

end
