/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.HierarchyCaseThreePreparation
public import LeanPool.GoldbergSeymour.HierarchySituationTwoOutsidePenultimateReconstruction
public import LeanPool.GoldbergSeymour.TashkinovSeriesNonParallelClosed

/-!
# Hierarchy Situation Two Case Three Normalization

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable def helperGoodShort1489.{u_1, u_2} :
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
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (C : HierarchyCounterexample base) →
  (ctx :
      HierarchyMinimumCounterexampleContext G k e0 input T phi ett
        base C) →
  (D :
      HierarchySituationTwoCaseThreeData G k e0 input T phi ett
        base C ctx) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree n.castSucc;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := T.length - A.length;
  let B : TreeSequence G e0 :=
    HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
  let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
  (beta : Fin k) →
  let Bplus : TreeSequence G e0 :=
    HierarchyFullTailPrefix C
      (HierarchyFullTailLength C - (1 : ℕ));
  (hlenB : B.length = T.length - (2 : ℕ)) →
  (hBT : TreeSequenceInitialSegment B T) →
  D.alpha ≠ beta →
  (segTrans :
      ∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W →
            TreeSequenceInitialSegment S W) →
  (equalTrees :
      ∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          S.length = U.length → S = U) →
  (m : ℕ) →
  (1 : ℕ) ≤ m →
  (pv : Fin (m + (1 : ℕ)) → V) →
  let R : TreeSequence G e0 :=
    if
        pv (0 : Fin (m + (1 : ℕ))) =
          T.vertex
            D.penultimateVertexIndex then
      Bplus
    else B;
  TreeSequenceInitialSegment B R →
  TreeSequenceInitialSegment R T →
  (Utree : TreeSequence G e0) →
  TreeSequenceInitialSegment R Utree →
  (∀ (r : Fin Utree.length),
      R.length ≤ (↑r : ℕ) →
        Utree.vertex r.succ ∉
            TreeSequenceVertexSet
              R ∧
          Sum.inr (Utree.edge r) ∈
              TwoColorComponent G
                phi D.alpha beta
                (Sum.inl
                  (T.vertex
                    D.terminalVertexIndex)) ∧
            Sum.inl
                  (Utree.vertex
                    r.succ) ∈
                TwoColorComponent G
                  phi D.alpha beta
                  (Sum.inl
                    (T.vertex
                      D.terminalVertexIndex)) ∧
              (phi (Utree.edge r) =
                    some D.alpha ∨
                  phi
                      (Utree.edge
                        r) =
                    some beta) ∧
                G.ends
                    (Utree.edge r) =
                  if
                      (↑r : ℕ) =
                        R.length then
                    s(pv
                        (0 :
                          Fin
                            (m +
                              (1 :
                                ℕ))),
                      Utree.vertex
                        r.succ)
                  else
                    s(Utree.vertex
                        r.castSucc,
                      Utree.vertex
                        r.succ)) →
  (hBU :
      TreeSequenceInitialSegment B
        Utree) →
  (hAU :
      TreeSequenceInitialSegment
        A Utree) →
  (corrU :
      CorrespondingExtendedTashkinovTree
        G k e0 ett phi
        Utree) →
  (baseU :
      HierarchyBase
        corrU.replacementETT
        phi) →
  (hcoreU :
      baseU.core =
        base.core) →
  baseU.closure =
      base.closure →
  (terminalData :
      corrU.replacementETT.series.data.tree
            (Fin.last
                corrU.replacementETT.rounds).castSucc =
          Tn ∧
        corrU.replacementETT.series.data.kind
            (Fin.last
              corrU.replacementETT.rounds) =
          ett.series.data.kind
            n) →
  (ordinaryToA :
      ∀
        (j :
          Fin
            (H.dividerCount +
              (1 :
                ℕ))),
        TreeSequenceInitialSegment
          (H.stage
            j.castSucc)
          A) →
  (hAUstrict :
      A.length <
        Utree.length) →
  let newStage :
    Fin
        (H.dividerCount +
          (2 :
            ℕ)) →
      TreeSequence
        G e0 :=
    fun
      (j :
        Fin
          (H.dividerCount +
            (2 :
              ℕ))) ↦
    if
        (↑j :
            ℕ) =
          H.dividerCount +
            (1 :
              ℕ) then
      Utree
    else
      H.stage j;
  (stageOld :
      ∀
        (j :
          Fin
            (H.dividerCount +
              (1 :
                ℕ))),
        newStage
            j.castSucc =
          H.stage
            j.castSucc) →
  (stageLast :
      newStage
          (Fin.last
            (H.dividerCount +
              (1 :
                ℕ))) =
        Utree) →
  (stageAt :
      ∀
        (j :
          Fin
            (H.dividerCount +
              (2 :
                ℕ))),
        (↑j :
              ℕ) ≤
            H.dividerCount →
          newStage
              j =
            H.stage
              j) →
  (divBound :
      ∀
        (i :
          Fin
            H.dividerCount),
        (↑(H.dividerPosition
                i) :
            ℕ) ≤
          B.length) →
  let
    K :
    TashkinovHierarchy
      corrU.replacementETT
      baseU :=
    HierarchyCaseThreePreparation.helperK553
      G
      k
      e0
      input
      T
      phi
      ett
      base
      C
      ctx
      D
      hlenB
      hBT
      segTrans
      equalTrees
      m
      pv
      Utree
      hBU
      hAU
      corrU
      baseU
      hcoreU
      terminalData
      ordinaryToA
      hAUstrict
      stageOld
      stageLast
      stageAt
      divBound;
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 :
              ℕ))),
      K.stage
          j.castSucc =
        H.stage
          j.castSucc) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 :
              ℕ))),
      HierarchyStarredStage
          K
          j =
        HierarchyStarredStage
          H
          j) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 :
              ℕ))),
      HierarchyStoredColorsAt
          K
          j =
        HierarchyStoredColorsAt
          H
          j) →
  (∀
      (j :
        Fin
          (H.dividerCount +
            (1 :
              ℕ))),
      HierarchyStageMissingColors
          K
          j =
        HierarchyStageMissingColors
          H
          j) →
  (∀
      (i :
        Fin
          H.dividerCount)
      (eta :
        Fin
          k),
      HierarchySegmentColors
          K
          i.castSucc
          eta =
        HierarchySegmentColors
          H
          i.castSucc
          eta) →
  beta ∉
      Gamma →
  (∀
      (S :
        TreeSequence
          G
          e0)
      (c :
        Fin
          k)
      (i :
        Fin
          (S.length +
            (1 :
              ℕ))),
      c ∈
          MissingColors
            G
            phi
            (S.vertex
              i) →
        (↑(HierarchyFirstMissingPosition
                phi
                S
                c) :
            ℕ) ≤
          (↑i :
            ℕ)) →
  (∀
      (c :
        Fin
          k),
      (↑(HierarchyFirstMissingPosition
                phi
                T
                c) :
            ℕ) <
          T.length →
        c ∈
          MissingColors
            G
            phi
            (T.vertex
              (HierarchyFirstMissingPosition
                phi
                T
                c))) →
  (∀
      eta ∈
        Dnq,
      D.alpha ∈
          C.good.gamma
            q
            eta →
        (↑(HierarchyFirstMissingPosition
                phi
                T
                eta) :
            ℕ) ≤
          B.length) →
  GoodHierarchy
    K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dnq Gamma beta Bplus
      hlenB hBT hne segTrans equalTrees m hm pv R hBR hRT Utree hRU hnew hBU hAU corrU baseU
      hcoreU hclosureU terminalData ordinaryToA hAUstrict newStage stageOld stageLast stageAt
      divBound K stageEq starredEq storedEq missingEq internalSegmentEq betaOutsideGamma
      firstBound firstWitness control
  clear * - G phi K C H q A B T Utree R hRU hRT hnew hBR hBT hBU control
    storedEq missingEq starredEq stageEq internalSegmentEq terminalData hcoreU hclosureU
    firstWitness firstBound betaOutsideGamma Dnq beta D hlenB
  have terminalAvoid (eta : Fin k) (heta : eta ∈ Dnq) :
      Disjoint (C.good.gamma q eta) (HierarchySegmentColors K q eta) := by
    exact HierarchyCaseThreePreparation.helper_terminalAvoid_1779
      G k e0 input T phi ett base C ctx D beta hlenB hBT segTrans equalTrees m pv hBR hRT
      Utree hRU hnew hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict
      stageOld stageLast stageAt divBound starredEq betaOutsideGamma firstBound firstWitness
      control eta heta
  exact {
    gamma := C.good.gamma
    twoColors := by intro j eta heta; exact C.good.twoColors j eta ((storedEq j) ▸ heta)
    avoidance := by
      intro j eta heta c hc
      have hetaOld : eta ∈ HierarchyStoredColorsAt H j := (storedEq j) ▸ heta
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [missingEq j]
        exact (Finset.mem_sdiff.mp (C.good.avoidance j eta hetaOld hc)).1
      · intro hseg
        by_cases hj : j.val < H.dividerCount
        · let i : Fin H.dividerCount := ⟨j.val, hj⟩
          have hij : i.castSucc = j := Fin.ext rfl
          rw [← hij, internalSegmentEq i eta, hij] at hseg
          exact (Finset.mem_sdiff.mp (C.good.avoidance j eta hetaOld hc)).2 hseg
        · have he : j = q := Fin.ext (by
            change j.val = H.dividerCount
            have hjb : j.val < H.dividerCount + 1 := j.isLt
            omega)
          subst j
          exact Finset.disjoint_left.mp (terminalAvoid eta hetaOld) hc hseg
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta ((storedEq j) ▸ heta) ((storedEq j) ▸ htheta) hne
    uniqueRefresh := by
      intro i
      rw [storedEq i.succ, stageEq i.succ, starredEq i.castSucc]
      exact C.good.uniqueRefresh i
    parallelBase := by
      dsimp only
      intro hp
      have hpo : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.symm.trans hp
      rw [hcoreU, hclosureU, terminalData.1, storedEq 0]
      exact C.good.parallelBase hpo
    minusClosed := by
      intro i
      rw [stageEq i.succ, storedEq i.succ]
      exact C.good.minusClosed i }

private theorem helper_continuation_850.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c} : Finset (Fin k));
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let _ : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) →
    ∀ (hlenB : B.length = T.length - (2 : ℕ)), Bplus.length = T.length - (1 : ℕ) →
    ∀ (hBT : TreeSequenceInitialSegment B T), TreeSequenceInitialSegment Bplus T →
        TreeSequenceInitialSegment B Bplus → (↑D.earlierVertexIndex : ℕ) < B.length + (1 : ℕ) →
        beta ∈ TreeMissingColors phi Bplus → D.alpha ∈ TreeMissingColors phi Bplus → D.alpha ≠
        beta → T.vertex D.terminalVertexIndex ∉ TreeSequenceVertexSet Bplus →
    ∀ (segTrans :
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) (equalTrees :
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S U → S.length = U.length → S = U),
        (H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) → TreeSequenceInitialSegment A T →
        TreeSequenceInitialSegment Tn A → D.alpha ∈ TreeMissingColors phi B →
    ∀ (m : ℕ), (1 : ℕ) ≤ m →
    ∀ (pv : Fin (m + (1 : ℕ)) → V),
    let R : TreeSequence G e0 := if pv (0 : Fin (m + (1 : ℕ))) = T.vertex D.penultimateVertexIndex
        then Bplus else B; TreeSequenceInitialSegment B R →
    ∀ (Utree : TreeSequence G e0), TreeSequenceInitialSegment R Utree → Utree.length = R.length +
        m → R.length < Utree.length → (
    ∀ (r : Fin Utree.length), R.length ≤ (↑r : ℕ) → Utree.vertex r.succ ∉ TreeSequenceVertexSet R
        ∧ Sum.inr (Utree.edge r) ∈ TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)) ∧ Sum.inl (Utree.vertex r.succ) ∈ TwoColorComponent G phi D.alpha
        beta (Sum.inl (T.vertex D.terminalVertexIndex)) ∧ (phi (Utree.edge r) = some D.alpha ∨ phi
        (Utree.edge r) = some beta) ∧ G.ends (Utree.edge r) = if (↑r : ℕ) = R.length then s(pv (0
        : Fin (m + (1 : ℕ))), Utree.vertex r.succ) else s(Utree.vertex r.castSucc, Utree.vertex
        r.succ)) →
    ∀ (hBU : TreeSequenceInitialSegment B Utree) (hAU : TreeSequenceInitialSegment A Utree),
        Utree.vertex (Fin.last Utree.length) = T.vertex D.terminalVertexIndex →
    ∀ (corrU : CorrespondingExtendedTashkinovTree G k e0 ett phi Utree), MaximumProperty
        corrU.replacementETT →
    ∀ (baseU : HierarchyBase corrU.replacementETT phi) (hcoreU : baseU.core = base.core)
        (terminalData : corrU.replacementETT.series.data.tree (Fin.last
        corrU.replacementETT.rounds).castSucc = Tn ∧ corrU.replacementETT.series.data.kind
        (Fin.last corrU.replacementETT.rounds) = ett.series.data.kind n) (ordinaryToA :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage j.castSucc) A)
        (hAUstrict : A.length < Utree.length),
    let newStage : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 := fun (j : Fin
        (H.dividerCount + (2 : ℕ))) ↦ if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then Utree else
        H.stage j;
    ∀ (stageOld :
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), newStage j.castSucc = H.stage j.castSucc) (stageLast :
        newStage (Fin.last (H.dividerCount + (1 : ℕ))) = Utree) (stageAt :
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))), (↑j : ℕ) ≤ H.dividerCount → newStage j = H.stage j)
        (divBound :
    ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) ≤ B.length),
    let K : TashkinovHierarchy corrU.replacementETT baseU :=
        HierarchyCaseThreePreparation.helperK553 G k e0 input T phi ett base C ctx D hlenB hBT
        segTrans equalTrees m pv Utree hBU hAU corrU baseU hcoreU terminalData ordinaryToA
        hAUstrict stageOld stageLast stageAt divBound; (
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = HierarchyStarredStage H j)
        → (
    ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))), c ∈ MissingColors G phi
        (S.vertex i) → (↑(HierarchyFirstMissingPosition phi S c) : ℕ) ≤ (↑i : ℕ)) → (
    ∀ (c : Fin k), (↑(HierarchyFirstMissingPosition phi T c) : ℕ) < T.length → c ∈ MissingColors G
        phi (T.vertex (HierarchyFirstMissingPosition phi T c))) →
    ∀ (_ : (
    ∀ eta ∈ Dnq, D.alpha ∈ C.good.gamma q eta → (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤
        B.length) → GoodHierarchy K),
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative Bplus Q hbetaPresent hlenB hlenPlus hBT hplusT hBBplus
      hindex hbetaMissingPlus halphaMissingPlus hne hterminalOutside segTrans equalTrees
      lastPositive hAT hTnA halphaMissingB m hm pv R hBR Utree hRU hUlen hRUstrict hnew hBU hAU
      hUterminal corrU hMPU baseU hcoreU terminalData ordinaryToA hAUstrict newStage stageOld
      stageLast stageAt divBound K starredEq firstBound firstWitness goodShort
  have pathShort : HierarchyPathNumber K < HierarchyPathNumber H := by
    exact HierarchyCaseThreePreparation.helper_pathShort_734
      G k e0 input T phi ett base C ctx D beta hlenB hlenPlus hBT hplusT segTrans equalTrees
      hAT m hm pv hBR Utree hRU hUlen hRUstrict hnew hBU hAU corrU baseU hcoreU terminalData
      ordinaryToA hAUstrict stageOld stageLast stageAt divBound starredEq
  have shorteningContradiction
      (control : ∀ eta, eta ∈ Dnq → D.alpha ∈ C.good.gamma q eta →
        (HierarchyFirstMissingPosition phi T eta).val ≤ B.length) : False := by
    have hnotElementary : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet Utree) := by
      let iB : Fin (B.length + 1) := ⟨D.earlierVertexIndex.val, hindex⟩
      have hvB : B.vertex iB = T.vertex D.earlierVertexIndex := by
        rw [← hBT.2.1 iB]
        congr 1
      have hvU : T.vertex D.earlierVertexIndex ∈ TreeSequenceVertexSet Utree :=
        TreeSequenceInitialSegmentVertexSetSubset hBU (hvB ▸ (by simp [TreeSequenceVertexSet]))
      have htU : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet Utree :=
        hUterminal ▸ (by simp [TreeSequenceVertexSet])
      have hdistinct : T.vertex D.earlierVertexIndex ≠ T.vertex D.terminalVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hterm := D.terminalVertexPosition
        have hearly := D.earlierVertexBeforePenultimate
        have hpen := D.penultimateVertexPosition
        omega
      intro he
      exact Finset.disjoint_left.mp (he hvU htU hdistinct)
        D.alphaMissingEarlier D.alphaMissingTerminal
    let Cnew : HierarchyCounterexample baseU := {
      positive := by rw [corrU.rungAgreement]; exact C.positive
      hierarchy := K
      good := goodShort control
      maximum := hMPU
      notElementary := hnotElementary }
    exact ctx.lexicographicMinimality Cnew corrU.rungAgreement rfl (Or.inl pathShort)
  by_cases haOutside : D.alpha ∉ Gamma
  · exact (shorteningContradiction (by
      intro eta heta ha
      exact (haOutside (Finset.mem_biUnion.mpr ⟨eta, heta, ha⟩)).elim)).elim
  · have haGamma : D.alpha ∈ Gamma := not_not.mp haOutside
    by_cases haUsed : D.alpha ∈ tailUsed
    · exact HierarchyCaseThreePreparation.helper_branch_1316
        G k e0 input T phi ett base C ctx D beta hlenB hlenPlus hBT hne segTrans equalTrees
        lastPositive m pv Utree hBU hAU corrU baseU hcoreU terminalData ordinaryToA hAUstrict
        stageOld stageLast stageAt divBound shorteningContradiction haUsed
    -- An unused reserved color requires a genuinely recolored certificate.
    · exact @HierarchyCaseThreePreparation.helper_branch_1551 (@V) (@E) inferInstance
        inferInstance inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
        (@base) (@C) (@ctx) (@D) (@beta) (@hmissing) (@hunused) (@halternative) (@hbetaPresent)
        (@hlenB) (@hlenPlus) (@hBT) (@hplusT) (@hBBplus) (@hbetaMissingPlus) (@halphaMissingPlus)
        (@hne) (@hterminalOutside) (@lastPositive) (@hAT) (@hTnA) (@halphaMissingB) (@m) (@hm)
        (@firstBound) (@firstWitness) (@haGamma) (@haUsed)
private theorem helper_continuation_647.{u_1, u_2} :
    HierarchyCaseThreePreparation.helperContinuation647Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative Bplus Q hbetaPresent hlenB hlenPlus hBT hplusT hBBplus
      hindex hbetaMissingPlus halphaMissingPlus hne hterminalOutside segTrans equalTrees
      stageSegment lastPositive hAT hAB hTnA halphaMissingB m hm pv R hBR hRT Utree hRU hUlen
      hRUstrict hnew hBU hAU hTnU hTnUstrict hUterminal hmod heligible
  obtain ⟨corrU⟩ := hmod.2.2 Utree hTnU hTnUstrict heligible
  have hMPU := MaximumPropertyTransport G k e0 ett phi hmod Utree corrU C.maximum
  obtain ⟨baseU, hcoreU, hclosureU, hsupportU⟩ :=
    HierarchyBaseCorrespondingTransport G k e0 input T Utree phi ett corrU base
  have terminalData :
      corrU.replacementETT.series.data.tree (Fin.last corrU.replacementETT.rounds).castSucc = Tn ∧
      corrU.replacementETT.series.data.kind (Fin.last corrU.replacementETT.rounds) =
        ett.series.data.kind n := by
    exact ⟨corrU.terminalData.1, corrU.terminalData.2.1⟩
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    exact H.stageInitialSegmentOfStarredStage j (Fin.last H.dividerCount) (Fin.le_last _)
  have hAUstrict : A.length < Utree.length := lt_of_le_of_lt (segTrans hAB hBR).1 hRUstrict
  let newStage : Fin (H.dividerCount + 2) → TreeSequence G e0 := fun j =>
    if j.val = H.dividerCount + 1 then Utree else H.stage j
  have stageOld (j : Fin (H.dividerCount + 1)) : newStage j.castSucc = H.stage j.castSucc := by
    simp only [newStage]
    rw [ite_eq_right (by have := j.isLt; change j.val ≠ H.dividerCount + 1; omega)]
  have stageLast : newStage (Fin.last (H.dividerCount + 1)) = Utree := by simp [newStage]
  have stageAt (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
      newStage j = H.stage j := by
    simp only [newStage, ite_eq_right (by omega : j.val ≠ H.dividerCount + 1)]
  have divBound (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
    have hl : (H.stage i.succ.castSucc).length = (H.dividerPosition i).val := by
      have he := congrArg TreeSequence.length (H.dividerStage i)
      exact he
    have hs := (segTrans (ordinaryToA i.succ) hAB).1
    omega
  let K : TashkinovHierarchy corrU.replacementETT baseU := by
    exact @HierarchyCaseThreePreparation.helperK553 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@hlenB) (@hBT) (@segTrans) (@equalTrees) (@m) (@pv) (@Utree) (@hBU) (@hAU)
        (@corrU) (@baseU) (@hcoreU) (@terminalData) (@ordinaryToA) (@hAUstrict) (@stageOld)
        (@stageLast) (@stageAt) (@divBound)
  have stageEq (j : Fin (H.dividerCount + 1)) : K.stage j.castSucc = H.stage j.castSucc :=
      stageOld j
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hcoreU
    · exact stageEq i.succ
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [P2752_T2_TerminalStoredColors ett corrU, starredEq]
  have missingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact congrArg (TreeMissingColors phi) terminalData.1
    · exact congrArg (TreeMissingColors phi) (stageEq i.succ)
  have internalSegmentEq (i : Fin H.dividerCount) (eta : Fin k) :
      HierarchySegmentColors K i.castSucc eta = HierarchySegmentColors H i.castSucc eta := by
    let S := H.stage i.succ.castSucc
    have hSB := segTrans (ordinaryToA i.succ) hAB
    have hcutT := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta S.length hSB.1
    have hcutU := HierarchyFirstMissingPositionPrefixCutoff phi B Utree hBU eta S.length hSB.1
    unfold HierarchySegmentColors
    have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
    dsimp only
    rw [hi, stageEq i.succ, starredEq i.castSucc, ← hcutU, hcutT]
  have betaOutsideGamma : beta ∉ Gamma := by
    rcases halternative with h | h | h
    · exact h.2.2
    · exact h.2.2
    · intro hg
      exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2 hg h.1
  have firstBound (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + 1))
      (hc : c ∈ MissingColors G phi (S.vertex i)) :
      (HierarchyFirstMissingPosition phi S c).val ≤ i.val := by
    exact TreeSequenceFirstMissingPositionLe hc
  have firstWitness (c : Fin k) (hc : (HierarchyFirstMissingPosition phi T c).val < T.length) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
    exact TreeSequenceFirstMissingPositionMem hc
  have goodShort := @helperGoodShort1489 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta)
      (@hlenB) (@hBT) (@hne) (@segTrans) (@equalTrees) (@m) (@hm) (@pv) (@hBR) (@hRT) (@Utree)
      (@hRU) (@hnew) (@hBU) (@hAU) (@corrU) (@baseU) (@hcoreU) (@hclosureU) (@terminalData)
      (@ordinaryToA) (@hAUstrict) (@stageOld) (@stageLast) (@stageAt) (@divBound) (@stageEq)
      (@starredEq) (@storedEq) (@missingEq) (@internalSegmentEq) (@betaOutsideGamma) (@firstBound)
      (@firstWitness)
  exact @helper_continuation_850 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta)
      (@hmissing) (@hunused) (@halternative) (@hbetaPresent) (@hlenB) (@hlenPlus) (@hBT)
      (@hplusT) (@hBBplus) (@hindex) (@hbetaMissingPlus) (@halphaMissingPlus) (@hne)
      (@hterminalOutside) (@segTrans) (@equalTrees) (@lastPositive) (@hAT) (@hTnA)
      (@halphaMissingB) (@m) (@hm) (@pv) (@hBR) (@Utree) (@hRU) (@hUlen) (@hRUstrict) (@hnew)
      (@hBU) (@hAU) (@hUterminal) (@corrU) (@hMPU) (@baseU) (@hcoreU) (@terminalData)
      (@ordinaryToA) (@hAUstrict) (@stageOld) (@stageLast) (@stageAt) (@divBound) (@starredEq)
      (@firstBound) (@firstWitness) (@goodShort)
private theorem helper_heligible_1741.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ)); (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) →
    ∀ (m : ℕ) (pv : Fin (m + (1 : ℕ)) → V),
    let R : TreeSequence G e0 := if pv (0 : Fin (m + (1 : ℕ))) = T.vertex D.penultimateVertexIndex
        then Bplus else B; TreeSequenceInitialSegment R T →
    ∀ (Utree : TreeSequence G e0), TashkinovAugmentationSequence phi R Utree →
        TreeSequenceInitialSegment Tn R → (
    ∀ (S : TreeSequence G e0) (colors : Finset (Fin k)) (psi : PartialEdgeColoring E k),
        IsProperEdgeColoring G psi → IsOneEdgeUncolored psi e0 → ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet S) → StableColoring S colors psi phi → ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet S)) → (
    ∀ (f : E) (seed : TreeSequence G e0), ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn)
        → TreeSequenceAdjoinEdge Tn f seed → TashkinovClosure phi seed (ett.series.data.tree
        (Fin.last (ett.rounds + (1 : ℕ)))) → TashkinovAugmentationSequence phi seed Utree) →
        ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn Utree ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed Utree := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Bplus segTrans m pv R
      hRT Utree hRUroute hTnR stableClosed seededRoute
  have hs := ett.series.certified n
  have hcolorN : ett.series.data.coloring n = phi := ett.generatingColoring.symm
  have hnNext : n.succ = Fin.last (ett.rounds + 1) := Fin.ext rfl
  generalize hn : n = z at hs
  cases hs with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
    have hv := congrArg Fin.val hn
    have hp := C.positive
    dsimp [n] at hv
    omega
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    have hi : i.succ = n := hn.symm
    have hclosure : TashkinovClosure phi Tn
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa only [hi, hcolorN, hnNext] using closedExtension
    refine Or.inl ⟨by simpa only [hi] using currentKind, ?_⟩
    exact (TashkinovAugmentationSequenceRestrict phi Tn R _ hclosure.1 hTnR
      (segTrans hRT ett.belowFinal)).trans hRUroute
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hi : i.succ = n := hn.symm
    have htree : ett.series.data.tree i.succ.castSucc = Tn :=
      congrArg (fun j : Fin (ett.rounds + 1) => ett.series.data.tree j.castSucc) hi
    have hselected : choice.selected = phi := currentColoring.symm.trans
      ((congrArg ett.series.data.coloring hi).trans ett.generatingColoring.symm)
    have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) :=
      stableClosed Tn _ _ previousProper previousOneUncolored
        (htree ▸ previousClosed) (by simpa only [htree, hselected] using choice.selectedStable)
    have hseed : TreeSequenceAdjoinEdge Tn choice.edge adjoined := htree ▸ adjoinedExactly
    have hclosure : TashkinovClosure phi adjoined
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa only [hi, hcolorN, hnNext] using closedExtension
    exact Or.inr ⟨Or.inl (by simpa only [hi] using currentKind), choice.edge, adjoined,
      by simpa only [hi] using currentEdges, hseed, seededRoute _ _ hclosed hseed hclosure⟩
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    have hi : i.succ = n := hn.symm
    have htree : ett.series.data.tree i.succ.castSucc = Tn :=
      congrArg (fun j : Fin (ett.rounds + 1) => ett.series.data.tree j.castSucc) hi
    have hcolor : ett.series.data.coloring i.castSucc = phi := currentColoring.symm.trans
      ((congrArg ett.series.data.coloring hi).trans ett.generatingColoring.symm)
    have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) := by
      have hc : ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
          (TreeSequenceVertexSet Tn) := by
        rw [← htree]
        exact previousClosed
      exact @Eq.mp _ _ (congrArg (fun psi => ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet Tn)) hcolor) hc
    have hseed : TreeSequenceAdjoinEdge Tn available.edge adjoined := htree ▸ adjoinedExactly
    have hclosure : TashkinovClosure phi adjoined
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa only [hi, hcolorN, hnNext] using closedExtension
    exact Or.inr ⟨Or.inr (by simpa only [hi] using currentKind), available.edge, adjoined,
      by simpa only [hi] using currentEdges, hseed, seededRoute _ _ hclosed hseed hclosure⟩

private theorem helper_continuation_547.{u_1, u_2} :
    HierarchyCaseThreePreparation.helperContinuation547Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative Bplus Q hbetaPresent hhit hlenB hlenPlus hBT hplusT
      hBBplus hindex hbetaMissingPlus halphaMissingPlus hne hterminalOutside segTrans
      commonPrefix equalTrees stageSegment lastPositive hAT
  have hAB : TreeSequenceInitialSegment A B :=
    commonPrefix hAT hBT
        (by have hp := D.tailAtLeastTwo; change 2 ≤ T.length - A.length at hp; omega)
  have hTnA : TreeSequenceInitialSegment Tn A := by
    exact base.lastRoundInitialSegmentCore.trans
      (H.coreInitialSegmentOfStarredStage (Fin.last _))
  have halphaMissingB : D.alpha ∈ TreeMissingColors phi B := by
    let i : Fin (B.length + 1) := ⟨D.earlierVertexIndex.val, hindex⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨B.vertex i, by simp [TreeSequenceVertexSet], ?_⟩
    have hv : B.vertex i = T.vertex D.earlierVertexIndex := by
      rw [← hBT.2.1 i]
      congr 1
    rw [hv]
    exact D.alphaMissingEarlier
  obtain ⟨m, hm, pv, pe, hpv, hpe, hstart, hlast, houtside,
      hvcomp, hecomp, hcolors, hends, hfresh⟩ :=
    TwoColorComponentNearestSegment G phi Bplus D.alpha beta
      (T.vertex D.terminalVertexIndex) ctx.proper hne hterminalOutside hhit
  let R := if pv 0 = T.vertex D.penultimateVertexIndex then Bplus else B
  have hBR : TreeSequenceInitialSegment B R := by
    dsimp [R]
    split
    · exact hBBplus
    · exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hRplus : TreeSequenceInitialSegment R Bplus := by
    dsimp [R]
    split
    · exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · exact hBBplus
  have hRT := segTrans hRplus hplusT
  have hstartR : pv 0 ∈ TreeSequenceVertexSet R := by
    clear * - R pv D B Bplus T hstart hlenB hlenPlus hplusT hBBplus
    dsimp [R]
    split
    · exact hstart
    · rename_i hnot
      have hs := hstart
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hs
      obtain ⟨i, hi⟩ := hs
      have hiB : i.val ≤ B.length := by
        by_contra hno
        have hiv : i.val = Bplus.length := by omega
        have hv : Bplus.vertex i = T.vertex D.penultimateVertexIndex := by
          rw [← hplusT.2.1 i]
          congr 1
          apply Fin.ext
          have hpen := D.penultimateVertexPosition
          change i.val = D.penultimateVertexIndex.val
          clear * - hpen hiv hlenPlus
          omega
        exact hnot (hi.symm.trans hv)
      let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨j, ?_⟩
      rw [← hBBplus.2.1 j]
      exact (congrArg Bplus.vertex (Fin.ext rfl)).trans hi
  obtain ⟨Utree, hRU, hUlen, hentries, hRUstrict, hRUroute, hUlast, hnew⟩ :=
    TashkinovAlternatingSegmentAppend G phi R D.alpha beta
      (T.vertex D.terminalVertexIndex) m hm pv pe hpv hpe hstartR
      (fun i hi => houtside i (TreeSequenceInitialSegmentVertexSetSubset hRplus hi))
      hvcomp hecomp hcolors hends
      (fun i j => by rw [← hRplus.2.2 j]; exact hfresh i _)
      (by obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp halphaMissingB
          exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBR hv, hc⟩)
      (by obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmissing
          exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBR hv, hc⟩)
  have hBU := segTrans hBR hRU
  have hAU := segTrans hAB hBU
  have hTnR := segTrans hTnA (segTrans hAB hBR)
  have hTnU := segTrans hTnR hRU
  have hTnUstrict : Tn.length < Utree.length := lt_of_le_of_lt hTnR.1 hRUstrict
  have hUterminal : Utree.vertex (Fin.last Utree.length) = T.vertex D.terminalVertexIndex :=
    hUlast.trans hlast
  have hmod := Td G k e0 input T phi ett C.maximum C.positive ctx.lowerRung
    phi ctx.proper ctx.oneEdgeUncolored (by rw [← ett.generatingColoring]; simp [StableColoring])
  have stableClosed (S : TreeSequence G e0) (colors : Finset (Fin k))
      (psi : PartialEdgeColoring E k)
      (hppsi : IsProperEdgeColoring G psi) (hopsi : IsOneEdgeUncolored psi e0)
      (hcpsi : ColoredVertexSetClosed G psi (TreeSequenceVertexSet S))
      (hs : StableColoring S colors psi phi) :
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet S) := by
    exact StableColoring.closed S colors psi phi hppsi hopsi ctx.proper ctx.oneEdgeUncolored
      hcpsi hs
  -- The splice must retain the exact terminal SE/RE connecting seed.
  have seededRoute (f : E) (seed : TreeSequence G e0)
      (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn))
      (hseed : TreeSequenceAdjoinEdge Tn f seed)
      (hclosure : TashkinovClosure phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1)))) :
      TashkinovAugmentationSequence phi seed Utree := by
    have hstrict : Tn.length < R.length := by
      by_contra hno
      have hle := hTnR.1
      have heq : R = Tn := (equalTrees hTnR (by omega)).symm
      have hvinside : pv 0 ∈ TreeSequenceVertexSet Tn := heq ▸ hstartR
      let i : Fin m := ⟨0, by omega⟩
      have hvoutside : pv i.succ ∉ TreeSequenceVertexSet Tn := by
        intro hv
        exact houtside i (TreeSequenceInitialSegmentVertexSetSubset
          (segTrans hTnR hRplus) hv)
      have hbdy : pe i ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨pv 0, hvinside, pv i.succ, hvoutside, hends i⟩
      rcases hcolors i with hc | hc
      · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp halphaMissingB
        have hvn : v ∈ TreeSequenceVertexSet Tn :=
          heq ▸ TreeSequenceInitialSegmentVertexSetSubset hBR hv
        exact hclosed hbdy hvn hc hm
      · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
        have hvn : v ∈ TreeSequenceVertexSet Tn :=
          heq ▸ TreeSequenceInitialSegmentVertexSetSubset hBR hv
        exact hclosed hbdy hvn hc hm
    have hseedFinal := TashkinovAugmentationSequenceInitialSegment phi seed _ hclosure.1
    have hseedR : TreeSequenceInitialSegment seed R :=
      commonPrefix hseedFinal (segTrans hRT ett.belowFinal) (by obtain ⟨hl, _⟩ := hseed; omega)
    exact (TashkinovAugmentationSequenceRestrict phi seed R _ hclosure.1
      hseedR (segTrans hRT ett.belowFinal)).trans hRUroute
  have heligible :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn Utree) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed Utree) := by
    exact helper_heligible_1741 G k e0 input T phi ett base C ctx D segTrans m pv hRT Utree
      hRUroute hTnR stableClosed seededRoute
  exact @helper_continuation_647 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta)
      (@hmissing) (@hunused) (@halternative) (@hbetaPresent) (@hlenB) (@hlenPlus) (@hBT)
      (@hplusT) (@hBBplus) (@hindex) (@hbetaMissingPlus) (@halphaMissingPlus) (@hne)
      (@hterminalOutside) (@segTrans) (@equalTrees) (@stageSegment) (@lastPositive) (@hAT) (@hAB)
      (@hTnA) (@halphaMissingB) (@m) (@hm) (@pv) (@hBR) (@hRT) (@Utree) (@hRU) (@hUlen)
      (@hRUstrict) (@hnew) (@hBU) (@hAU) (@hTnU) (@hTnUstrict) (@hUterminal) (@hmod) (@heligible)
private theorem helper_branch_402.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let _ : Finset (Fin k) := {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi
        (T.edge r) = some c};
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := {c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c};
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed → beta ∉ MissingColors G phi
        (T.vertex D.terminalVertexIndex) →
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
        ℕ));
    let Q : Set (V ⊕ E) := TwoColorComponent G phi D.alpha beta (Sum.inl (T.vertex
        D.terminalVertexIndex)); beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) → (
    ∃ v ∈ TreeSequenceVertexSet Bplus, Sum.inl v ∈ Q) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B U Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative hterminal Bplus Q hbetaPresent hhit
  have hlenB : B.length = T.length - 2 := by
    have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    change min (A.length + (ell - 2)) T.length = T.length - 2
    dsimp [ell]
    omega
  have hlenPlus : Bplus.length = T.length - 1 := by
    have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    change min (A.length + (HierarchyFullTailLength C - 1)) T.length =
      T.length - 1
    change min (A.length + (ell - 1)) T.length = T.length - 1
    dsimp [ell]
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
  have hplusT : TreeSequenceInitialSegment Bplus T :=
    ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
  have hBBplus : TreeSequenceInitialSegment B Bplus := by
    have hle : B.length ≤ Bplus.length := by rw [hlenB, hlenPlus]; omega
    refine ⟨hle, ?_, ?_⟩
    · intro i
      exact (hplusT.2.1 (Fin.castLE (Nat.succ_le_succ hle) i)).symm.trans
        (hBT.2.1 i)
    · intro i
      exact (hplusT.2.2 (Fin.castLE hle i)).symm.trans (hBT.2.2 i)
  have hindex : D.earlierVertexIndex.val < B.length + 1 := by
    have hp := D.earlierVertexBeforePenultimate
    have hpen := D.penultimateVertexPosition
    have hp' : D.earlierVertexIndex.val + 1 < T.length := by
      omega
    rw [hlenB]
    omega
  have hindexPlus : D.earlierVertexIndex.val < Bplus.length + 1 := by
    rw [hlenPlus]
    have hp := D.earlierVertexBeforePenultimate
    have hpen := D.penultimateVertexPosition
    have hp' : D.earlierVertexIndex.val + 1 < T.length := by
      omega
    omega
  let jPlus : Fin (Bplus.length + 1) :=
    ⟨D.earlierVertexIndex.val, hindexPlus⟩
  have hvertexPlus : Bplus.vertex jPlus = T.vertex D.earlierVertexIndex := by
    have h := hplusT.2.1 jPlus
    calc
      Bplus.vertex jPlus = T.vertex (Fin.castLE
          (Nat.succ_le_succ hplusT.1) jPlus) := h.symm
      _ = T.vertex D.earlierVertexIndex := by
        apply congrArg T.vertex
        apply Fin.ext
        rfl
  have hbetaMissingPlus : beta ∈ TreeMissingColors phi Bplus := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBBplus hv, hm⟩
  have halphaMissingPlus : D.alpha ∈ TreeMissingColors phi Bplus := by
    apply Finset.mem_biUnion.mpr
    refine ⟨T.vertex D.earlierVertexIndex, ?_, D.alphaMissingEarlier⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨jPlus, hvertexPlus.symm⟩
  have hne : D.alpha ≠ beta := by
    intro he
    exact hterminal (he ▸ D.alphaMissingTerminal)
  have hterminalOutside : T.vertex D.terminalVertexIndex ∉
      TreeSequenceVertexSet Bplus := by
    intro hv
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    let iT : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hplusT.1) i
    have hprefix := hplusT.2.1 i
    have heq : iT = D.terminalVertexIndex := by
      apply T.vertex_injective
      calc
        T.vertex iT = Bplus.vertex i := hprefix.symm
        _ = T.vertex D.terminalVertexIndex := hi
    have hval : i.val = T.length := by
      have hx := congrArg Fin.val heq
      simpa [iT, D.terminalVertexPosition] using hx
    have hlenPlus' : Bplus.length + 1 = T.length := by
      rw [hlenPlus]
      have hTpos := T.positive
      omega
    have hi' : i.val < T.length := by
      rw [← hlenPlus']
      exact i.isLt
    rw [hval] at hi'
    exact (Nat.lt_irrefl _ hi')
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
      (hle : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
    exact hUW.of_common_extension hSW hle
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    exact hSU.eq_of_length_eq hlen
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩) (H.stage ⟨a + d, by omega⟩) := by
    exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    exact H.stageInitialSegment j
  have lastPositive (hp : H.dividerCount ≠ 0) : A = H.stage q.castSucc := by
    let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hi : q = i.succ := Fin.ext (by dsimp [q, i]; omega)
    change HierarchyStarredStage H q = H.stage q.castSucc
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hq : q = 0 := Fin.ext (by simp [q, hz])
      have hA : A = base.core := by simp [A, HierarchyStarredStage, hq]
      exact segTrans (hA ▸ H.coreInsideFirst) (stageToT ⟨1, by omega⟩)
    · rw [lastPositive hz]
      exact stageToT q.castSucc
  exact @helper_continuation_547 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta)
      (@hmissing) (@hunused) (@halternative) (@hbetaPresent) (@hhit) (@hlenB) (@hlenPlus) (@hBT)
      (@hplusT) (@hBBplus) (@hindex) (@hbetaMissingPlus) (@halphaMissingPlus) (@hne)
      (@hterminalOutside) (@segTrans) (@commonPrefix) (@equalTrees) (@stageSegment)
      (@lastPositive) (@hAT)
private theorem helper_branch_348.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let _ : Finset (Fin k) := {c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi
        (T.edge r) = some c};
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := Dnq.biUnion (C.good.gamma q);
    let tailUsed : Finset (Fin k) := {c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ phi (T.edge t) = some c};
    ∀ beta ∈ TreeMissingColors phi B, (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) → (0 : ℕ) <
        H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma ∨ H.dividerCount = (0 : ℕ) ∧ beta ∉ Dn ∧ beta ∉
        Gamma ∨ beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed → beta ∉ MissingColors G phi
        (T.vertex D.terminalVertexIndex) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Nonempty
        (HierarchySituationTwoCaseThreeNormalizedData G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Tn A ell B U Dn Dnq Gamma tailUsed
      beta hmissing hunused halternative hterminal
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  let Q := TwoColorComponent G phi D.alpha beta
    (Sum.inl (T.vertex D.terminalVertexIndex))
  have hbetaPresent : beta ∉ MissingColors G phi
      (T.vertex D.terminalVertexIndex) := hterminal
  by_cases hhit : ∃ v ∈ TreeSequenceVertexSet Bplus,
      Sum.inl v ∈ Q
  · exact helper_branch_402 G k e0 input T phi ett base C ctx D beta hmissing hunused
      halternative hterminal hbetaPresent hhit
  · have houtside : ∀ v : V, Sum.inl v ∈ Q →
        v ∉ TreeSequenceVertexSet Bplus := by
      intro v hv hvB
      exact hhit ⟨v, hvB, hv⟩
    obtain ⟨_, _, P, _, N, hN⟩ :=
      HierarchySituationTwoOutsidePenultimateReconstruction
        G k e0 input T phi ett base C ctx D beta hmissing hunused
        halternative hbetaPresent houtside
    exact ⟨P, ⟨N⟩⟩

theorem HierarchySituationTwoCaseThreeNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData
      G k e0 input T phi ett base C ctx) :
    ∃ P : HierarchyReplacementPresentation
        G k e0 input T phi ett base C ctx,
      Nonempty (HierarchySituationTwoCaseThreeNormalizedData
        G k e0 P.corresponding.replacementInput T P.coloring
          P.corresponding.replacementETT P.replacementBase
          P.counterexample P.minimumContext) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let A := HierarchyStarredStage H q
  let ell := T.length - A.length
  let B := HierarchyFullTailPrefix C (ell - 2)
  let M0 := (TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G phi v
  let U := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ r : Fin T.length, A.length ≤ r.val ∧
      r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let X := (TreeMissingColors phi B \ M0) \ U
  let Dn := TashkinovStoredColors ett.series.data n
  let Dnq := HierarchyStoredColorsAt H q
  let Gamma := Dnq.biUnion (C.good.gamma q)
  let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
    ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c
  -- Only the two terminal edges add obstructions to the color choice.
  have hchoice : ∃ beta : Fin k,
      beta ∈ TreeMissingColors phi B ∧
      (∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta) ∧
      ((0 < H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma) ∨
        (H.dividerCount = 0 ∧ beta ∉ Dn ∧ beta ∉ Gamma) ∨
        (beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed)) := by
    exact HierarchyCaseThreePreparation.helper_hchoice_125 G k e0 input T phi ett base C ctx D
  obtain ⟨beta, hmissing, hunused, halternative⟩ := hchoice
  by_cases hterminal : beta ∈ MissingColors G phi
      (T.vertex D.terminalVertexIndex)
  · exact HierarchyCaseThreePreparation.helper_branch_304 G k e0 input T phi ett base C ctx D
      beta hmissing hunused halternative hterminal
  · exact helper_branch_348 G k e0 input T phi ett base C ctx D beta hmissing hunused
      halternative hterminal
end GoldbergSeymour

end
