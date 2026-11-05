/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AlgorithmFiveFiveBaseStage

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTransTrees

public import LeanPool.GoldbergSeymour.ParallelBaseFourCommonMissingColors
public import LeanPool.GoldbergSeymour.ParallelClosureUnionElementary
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.ParallelCoreAugmentationStrict

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceStrictBoundaryWitness

public import LeanPool.GoldbergSeymour.PredecessorElementary
public import LeanPool.GoldbergSeymour.ClosedCoreElementary
public import LeanPool.GoldbergSeymour.CoreClosurePresentation

/-!
# Parallel Special Closure Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ParallelSpecialClosurePreparation
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett phi)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 2 * ett.rounds + 11 <=
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    TashkinovAugmentationSequence phi Tn base.core /\
      Tn.length < base.core.length /\
      (ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∨
        exists (U : TreeSequence G e0)
            (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
          MaximumProperty corrU.replacementETT /\
            TashkinovAugmentationSequence phi base.core U /\
            TreeSequenceInitialSegment base.core U /\
            base.core.length < U.length /\
            exists baseU : HierarchyBase corrU.replacementETT phi,
              baseU.core = base.core /\
                baseU.closure = base.closure /\
                baseU.supportPosition.val = base.supportPosition.val /\
                exists KU : TashkinovHierarchy corrU.replacementETT baseU,
                  KU.dividerCount = 0 /\
                    KU.stage 0 = Tn /\
                    KU.stage (Fin.last (KU.dividerCount + 1)) = U /\
                    exists goodU : GoodHierarchy KU,
                      (forall eta : Fin k,
                        eta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                          (goodU.gamma
                              (Fin.last KU.dividerCount) eta).card = 2 /\
                            goodU.gamma
                                (Fin.last KU.dividerCount) eta ⊆
                              TreeMissingColors phi Tn \
                                HierarchySegmentColors KU
                                  (Fin.last KU.dividerCount) eta) /\
                      (forall eta theta : Fin k,
                        eta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                        theta ∈ HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount) ->
                        eta ≠ theta ->
                          Disjoint
                            (goodU.gamma
                              (Fin.last KU.dividerCount) eta)
                            (goodU.gamma
                              (Fin.last KU.dividerCount) theta)) /\
                      (¬ TreeColorSetMinusClosed G phi base.core
                        ((HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount)).biUnion
                          (goodU.gamma (Fin.last KU.dividerCount)))) /\
                      4 <= ((TreeMissingColors phi Tn ∩
                            TreeMissingColors phi base.closure) \
                          (HierarchyStoredColorsAt KU
                            (Fin.last KU.dividerCount)).biUnion
                            (goodU.gamma
                              (Fin.last KU.dividerCount))).card /\
                      TreeColorSetMinusClosed G phi U
                        ((HierarchyTerminalStoredColors KU).biUnion
                          (goodU.gamma (Fin.last KU.dividerCount)))) := by
  classical
  dsimp only
  obtain ⟨hroute, hstrict⟩ := ParallelCoreAugmentationStrict ett base hPE
  refine ⟨hroute, hstrict, ?_⟩
  have hpositive : 0 < ett.rounds := by have := ett.roundsPositive; omega
  obtain ⟨hproper, hone, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi phi :=
    (sc2 G e0 _ _).refl ⟨phi, hproper, hone⟩
  have hcoreElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet base.core) :=
    ParallelClosureUnionElementary G k e0 input T phi ett hMP hpositive
      (by
        intro input' T' generating' lower hpos hlt hmax
        exact ⟨ctx.lowerOne lower hpos hlt hmax,
          ctx.lowerTwo lower hpos hlt hmax,
          ctx.lowerThree lower hpos hlt hmax,
          ctx.lowerFour lower hpos hlt hmax,
          ctx.lowerFive lower hpos hlt hmax,
          ctx.lowerSix lower hpos hlt hmax⟩)
      hPE phi hproper hone hstable base
  by_cases hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet base.core)
  · exact Or.inl
      (P2634_T1_ClosedCoreElementary ett hPE base.core hroute hcoreElementary hclosed)
  · apply Or.inr
    have hcommon := ParallelCommonMissingClosed G k e0 input T phi phi ett
      hpositive base ett.generatingColoring hPE
      (P2634_T1_PredecessorElementary G k e0 input T phi ett ctx hMP)
    have hfour := ParallelBaseFourCommonMissingColors ett base hPE hproper
      hone hdegree hcoreElementary
    have hmod : ModColoring ett phi :=
      Td G k e0 input T phi ett hMP hpositive
        (by
          intro input' T' generating' lower hpos hlt hmax
          exact ⟨ctx.lowerOne lower hpos hlt hmax,
            ctx.lowerTwo lower hpos hlt hmax,
            ctx.lowerThree lower hpos hlt hmax,
            ctx.lowerFour lower hpos hlt hmax,
            ctx.lowerFive lower hpos hlt hmax,
            ctx.lowerSix lower hpos hlt hmax⟩)
        phi hproper hone (by
          rw [← ett.generatingColoring]
          exact hstable)
    obtain ⟨Z, corrZ, hMPZ, hclosure, hfinal, hTn, hkind, baseZ,
        hcoreZ, hclosureZ, hsupportZ⟩ :=
      P2634_T1_CoreClosurePresentation G k e0 input T phi ett hMP hmod
        hPE base hroute hstrict
    have hnonclosedColor : ∃ alpha : Fin k,
        alpha ∈ TreeMissingColors phi base.core ∧
          ¬ TreeColorSetClosed G phi base.core {alpha} := by
      unfold ColoredVertexSetClosed at hclosed
      push Not at hclosed
      obtain ⟨f, alpha, v, hf, hv, hcolor, hmissing⟩ := hclosed
      refine ⟨alpha, Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩, ?_⟩
      intro h
      have hboundary : f ∈ BoundaryColorEdges G phi
          (TreeSequenceVertexSet base.core) alpha :=
        Finset.mem_filter.mpr ⟨hf, hcolor⟩
      rw [h alpha (Finset.mem_singleton_self alpha)] at hboundary
      simp at hboundary
    have hmodZ : ModColoring corrZ.replacementETT phi :=
      Td G k e0 corrZ.replacementInput Z phi corrZ.replacementETT hMPZ
        (by have := corrZ.replacementETT.roundsPositive; omega)
        (by
          intro input' T' generating' lower hpos hlt hmax
          rw [corrZ.rungAgreement] at hlt
          exact ⟨ctx.lowerOne lower hpos hlt hmax,
            ctx.lowerTwo lower hpos hlt hmax,
            ctx.lowerThree lower hpos hlt hmax,
            ctx.lowerFour lower hpos hlt hmax,
            ctx.lowerFive lower hpos hlt hmax,
            ctx.lowerSix lower hpos hlt hmax⟩)
        phi hproper hone (by
          rw [← corrZ.replacementETT.generatingColoring]
          exact (sc2 G e0 _ _).refl ⟨phi, hproper, hone⟩)
    obtain ⟨J, U, corrOne, hseed, hsequence, hsegment, hstrictPE,
        hstrictNonPE, hMPU, baseOne, hcoreOne, hclosureOne, hsupportOne,
        KOne, hzero, hstageZero, hstageLast, goodOne, hdata⟩ :=
      AlgorithmFiveFiveBaseStage G k e0 corrZ.replacementInput Z phi
        corrZ.replacementETT hMPZ hmodZ baseZ
        (by intro _; rw [hTn, hcoreZ]; exact hstrict)
        (by intro _; rw [hcoreZ, hfinal]; exact hclosure)
        (by rw [hTn, corrZ.rungAgreement]; exact hlarge)
        (by
          intro _
          rw [hcoreZ, hTn, hclosureZ]
          exact ⟨hnonclosedColor, hcommon, hfour⟩)
    have hJ : J = baseZ.core := by
      rcases hseed with hparallel | hnonparallel
      · exact hparallel.2
      · rcases hnonparallel.1 with hSE | hRE
        · rw [hkind] at hSE
          cases hSE
        · rw [hkind] at hRE
          cases hRE
    rw [hJ, hcoreZ] at hsequence hsegment
    have hstrictU : base.core.length < U.length := by
      rw [← hcoreZ]
      exact hstrictPE hkind
    have hcoreOut : baseOne.core = base.core := hcoreOne.trans hcoreZ
    have hclosureOut : baseOne.closure = base.closure :=
      hclosureOne.trans hclosureZ
    have hsupportOut : baseOne.supportPosition.val = base.supportPosition.val :=
      hsupportOne.trans hsupportZ
    rw [hTn] at hstageZero
    rcases hdata with ⟨⟨hpairs, hdisjoint, hparallel⟩, hminus⟩
    rw [hTn] at hpairs
    have hparallelOut := hparallel hkind
    rw [hcoreZ, hTn, hclosureZ] at hparallelOut
    obtain ⟨corrU, hinputU, hseriesU, hettU⟩ :=
      CorrespondingExtendedTashkinovTreeTransTrees G k e0 input T Z U
        phi phi phi ett corrZ corrOne
    refine ⟨U, corrU, ?_⟩
    -- Transport the dependent base, hierarchy, and good witness along one ETT equality.
    rcases corrU with ⟨inputOut, seriesOut, ettOut, hrOut, hsOut, hcOut,
      htOut, hdOut, heOut, hkOut, hpOut, hoOut, hstableOut⟩
    rcases corrOne with ⟨inputOne, seriesOne, ettOne, hrOne, hsOne, hcOne,
      htOne, hdOne, heOne, hkOne, hpOne, hoOne, hstableOne⟩
    dsimp only at hinputU hettU ⊢
    cases hinputU
    have hettEq : ettOut = ettOne := eq_of_heq hettU
    cases hettEq
    exact ⟨hMPU, hsequence, hsegment, hstrictU, baseOne, hcoreOut,
      hclosureOut, hsupportOut, KOne, hzero, hstageZero, hstageLast,
      goodOne, hpairs, hdisjoint, hparallelOut.1, hparallelOut.2, hminus⟩

end GoldbergSeymour

end
