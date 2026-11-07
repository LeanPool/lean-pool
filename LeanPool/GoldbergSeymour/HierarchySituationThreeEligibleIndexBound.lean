/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.SharedFacts.InsideAdvancement

public import LeanPool.GoldbergSeymour.HierarchyTailSwapData

public import LeanPool.GoldbergSeymour.SharedFacts.OutsideAdvancement

public import LeanPool.GoldbergSeymour.EligibleIndexBoundConstruction
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.StableChangeCaseThree
public import LeanPool.GoldbergSeymour.TerminalKempeStageSwitch
public import LeanPool.GoldbergSeymour.SharedFacts.ShorteningProofs

/-!
# Hierarchy Situation Three Eligible Index Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open EligibleIndexBound

private theorem helper_branch_2404.{u_1, u_2} :
    helperBranch2404Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A mu hlenT B hBlength r f S
      hSBlen beta hab sigma lastPositive positiveB aboveB strictB belowB generatingB baseB HB EB
      corr bs baseStageK terminalStageK nestedK strictK coreInsideK positiveK increasingK
      dividerStageK KF hpS lastOrdinary hlastLength hlt
  right
  refine ⟨Nat.le_antisymm hpS (by omega), ?_⟩
  have hidx : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
      (Fin.last HB.dividerCount).castSucc := Fin.ext rfl
  have hidxH : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
      (Fin.last H.dividerCount).castSucc := Fin.ext rfl
  rw [hidx, hidxH, lastOrdinary]
  dsimp only
  omega

private theorem helper_sameLast_4591.{u_1, u_2} :
    helperSameLast4591Conditions.{u_1, u_2} := by
  classical
  intro V E G e0 a b s t u v hab hst huv
  cases hab
  have he : s = t := eq_of_heq hst
  cases he
  cases huv
  rfl

private theorem helper_continuation_5341.{u_1, u_2} :
    helperContinuation5341Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower P alpha old H A n Tn mu hp
      hpUpper htail trans hlenT B X hBlength hXlength hBT hXB hTnX r f y consecutive hyf S hSBlen
      beta hbetaF z hzB hbetaz hzy hzX hab sigma fixed missingFixed fixedB missingTree minusEq
      lastPositive positiveB aboveB strictB belowB generatingB baseB HB hcountB hstagesB goodB EB
      coreBX closureBX corr hmaximum bs hcore hpe hclosure baseStageK terminalStageK nestedK
      strictK coreInsideK positiveK increasingK dividerStageK KF starredEq stageBX starBX
      allStageB terminalTree terminalStored
  have storedEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalStored, starredEq j, missingTree _ (starBX j)]
  have stageMissingEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStageMissingColors KF j = HierarchyStageMissingColors HB j := by
    exact helper_stageMissingEq_2235 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@hTnX) (@missingTree) (@positiveB) (@aboveB) (@strictB)
        (@belowB) (@generatingB) (@baseB) (@HB) (@corr) (@bs) (@baseStageK) (@terminalStageK)
        (@nestedK) (@strictK) (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK)
        (@stageBX) (@terminalTree) (@j)
  have earlyMissing (j : Fin (B.length + 1)) (hj : j.val < B.length) :
      MissingColors G sigma (B.vertex j) = MissingColors G mu (B.vertex j) := by
    exact helper_earlyMissing_2244 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@hBlength) (@hXlength) (@hXB) (@S) (@hSBlen) (@beta)
        (@hab) (@missingFixed) (@lastPositive) (@positiveB) (@aboveB) (@strictB) (@belowB)
        (@generatingB) (@baseB) (@HB) (@j) (@hj)
  -- Last-vertex changes preserve the totalized least missing position.
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (B.length + 1)) (hj : c ∈ MissingColors G psi (B.vertex j)) :
      (HierarchyFirstMissingPosition psi B c).val ≤ j.val := by
    exact TreeSequenceFirstMissingPositionLe hj
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi B c).val < B.length) :
      c ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B c)) := by
    exact TreeSequenceFirstMissingPositionMem hlt
  have firstEq (c : Fin k) : HierarchyFirstMissingPosition sigma B c =
      HierarchyFirstMissingPosition mu B c := by
    exact helper_firstEq_1174 G k e0 input T phi ett base C ctx P alpha hlenT hBlength S hSBlen
        positiveB aboveB strictB belowB generatingB baseB HB earlyMissing firstLe firstMem c
  have stageFixed (j : Fin (HB.dividerCount + 1)) (t : Fin (HB.stage j.succ).length) :
      sigma ((HB.stage j.succ).edge t) = mu ((HB.stage j.succ).edge t) := by
    rw [← (allStageB j.succ).2.2 t]
    exact fixedB _
  have segmentEq (j : Fin (HB.dividerCount + 1)) (c : Fin k) :
      HierarchySegmentColors KF j c = HierarchySegmentColors HB j c := by
    apply helper_segmentEq_2283 <;> assumption
  let goodS : GoodHierarchy KF := by
    exact @helperGoodS3640 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hp)
        (@hlenT) (@hTnX) (@missingFixed) (@missingTree) (@minusEq) (@positiveB) (@aboveB)
        (@strictB) (@belowB) (@generatingB) (@baseB) (@HB) (@goodB) (@coreBX) (@closureBX)
        (@corr) (@bs) (@hcore) (@hpe) (@hclosure) (@baseStageK) (@terminalStageK) (@nestedK)
        (@strictK) (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK) (@starredEq)
        (@stageBX) (@terminalTree) (@storedEq) (@stageMissingEq) (@segmentEq)
  have hbetaY : beta ∈ MissingColors G sigma y := by
    apply helper_hbetaY_2355 <;> assumption
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) := by
    exact helper_hnotElementary_2365 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@beta) (@z) (@hzB) (@hbetaz) (@hzy) (@hzX)
        (@missingFixed) (@hbetaY)
  let CS : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact old.positive
    hierarchy := KF
    good := goodS
    maximum := hmaximum
    notElementary := hnotElementary }
  have lastStar : HierarchyStarredStage KF (Fin.last KF.dividerCount) = A := by
    exact helper_lastStar_2378 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@hlenT) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB)
        (@baseB) (@HB) (@hcountB) (@hstagesB) (@corr) (@bs) (@baseStageK) (@terminalStageK)
        (@nestedK) (@strictK) (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK)
        (@starredEq)
  have hpS : HierarchyPathNumber KF ≤ HierarchyPathNumber H := by
    exact helper_hpS_844 G k e0 input T phi ett base C ctx hpathLower P alpha hp hpUpper htail
        hlenT hBT consecutive S hSBlen beta hab lastPositive positiveB aboveB strictB belowB
        generatingB baseB HB corr bs baseStageK terminalStageK nestedK strictK coreInsideK
        positiveK increasingK dividerStageK lastStar
  have lastOrdinary : HB.stage (Fin.last HB.dividerCount).castSucc =
      H.stage (Fin.last H.dividerCount).castSucc := by
    apply helper_lastOrdinary_2387 <;> assumption
  have hlastLength : (H.stage (Fin.last H.dividerCount).castSucc).length < B.length := by
    have hh := HB.strict (Fin.last HB.dividerCount)
    simpa only [lastOrdinary, Fin.succ_last, HB.terminalStage] using hh
  -- The comparison is at the original rung and divider count.
  apply P.minimumContext.lexicographicMinimality CS corr.rungAgreement hcountB
  change HierarchyCounterexampleLess
    (HierarchyPathNumber KF, B.length - (HB.stage ⟨HB.dividerCount, by omega⟩).length)
    (HierarchyPathNumber H, T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
  by_cases hlt : HierarchyPathNumber KF < HierarchyPathNumber H
  · exact Or.inl hlt
  · apply helper_branch_2404 <;> assumption
private theorem helper_continuation_5697.{u_1, u_2} :
    helperContinuation5697Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower P alpha old H A n Tn mu hp
      hpUpper htail trans chain coreA hTnA hlenT B X hBlength hXlength hBT hAX hXB hTnX hAB r f y
      w consecutive hends hyf S hSBlen beta hbetaF z hzB hbetaz hzy hzX hab sigma fixed hsproper
      hsone incidentFixed missingFixed fixedB stable hrouteB missingTree
  have boundaryEq (U : TreeSequence G e0)
      (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (c : Fin k) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet U) c =
        BoundaryColorEdges G mu (TreeSequenceVertexSet U) c := by
    exact helper_boundaryEq_2121 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@hends) (@incidentFixed) (@U) (@hUX) (@c)
  have minusEq (U : TreeSequence G e0)
      (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R := by
    unfold TreeColorSetMinusClosed TreeColorSetClosed
    rw [missingTree U hUX]
    simp only [boundaryEq U hUX]
  have lastPositive (hq : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact helper_lastPositive_2137 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@hlenT) (@S) (@hSBlen) (@hq)
  have ordinaryA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    exact helper_ordinaryA_2146 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@chain) (@hTnA) (@hlenT) (@S) (@hSBlen) (@lastPositive) (@j)
  have starA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    refine Fin.cases coreA (fun i => ordinaryA i.succ) j
  -- Retain the old prefix data; construct the recolored ETT separately.
  obtain ⟨eb, hmaxB, hrungB, hseriesB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hdividersB, goodB, hcolorsB⟩ :=
    GoodHierarchyTerminalPrefixRepackage G k e0 P.corresponding.replacementInput T
      mu mu P.corresponding.replacementETT old.maximum P.replacementBase H old.good
      B hAB (by change A.length < B.length; omega) hBT
  rcases eb with ⟨roundsB, positiveB, seriesB, aboveB, strictB, belowB, generatingB⟩
  dsimp only at hrungB hseriesB
  cases hrungB
  have hs : seriesB = P.corresponding.replacementETT.series := eq_of_heq hseriesB
  cases hs
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu := {
    rounds := P.corresponding.replacementETT.rounds
    roundsPositive := positiveB
    series := P.corresponding.replacementETT.series
    abovePenultimate := aboveB
    strictAbovePenultimate := strictB
    belowFinal := belowB
    generatingColoring := generatingB }
  have coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X := by
    rw [hcoreB]
    exact TreeSequenceInitialSegmentVertexSetSubset (trans coreA hAX)
  have closureBX (hpe : EB.series.data.kind (Fin.last EB.rounds) =
      some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X := by
    exact helper_closureBX_2180 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@hlenT) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB)
        (@coreBX) (@hpe)
  -- PE preparation rebuilds the base; SE/RE retain the exact seed.
  have hdata : ∃ corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B,
      MaximumProperty corr.replacementETT ∧
      ∃ bs : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT bs,
          SameHierarchyStages HB K := by
    apply helper_hdata_519 <;> assumption
  obtain ⟨corr, hmaximum, bs, K, hsame⟩ := hdata
  let KF := K
  rcases hsame with ⟨hcore, hcount, hstage, hposition, hpe, hclosure⟩
  rcases K with ⟨qK, stageK, baseStageK, terminalStageK, nestedK, strictK,
    positionK, positiveK, increasingK, dividerStageK, coreInsideK⟩
  change HB.dividerCount = qK at hcount
  cases hcount
  have hs : HB.stage = stageK := eq_of_heq hstage
  cases hs
  have hpos : HB.dividerPosition = positionK := eq_of_heq hposition
  cases hpos
  have starredEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStarredStage KF j = HierarchyStarredStage HB j := by
    refine Fin.cases hcore.symm (fun _ => rfl) j
  have stageBX (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) X := by
    rw [(hstagesB j).1]
    exact trans (ordinaryA _) hAX
  have starBX (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceVertexSet (HierarchyStarredStage HB j) ⊆ TreeSequenceVertexSet X := by
    rw [(hstagesB j).2]
    exact TreeSequenceInitialSegmentVertexSetSubset (trans (starA _) hAX)
  have allStageB (j : Fin (HB.dividerCount + 2)) :
      TreeSequenceInitialSegment (HB.stage j) B := by
    exact Fin.reverseInduction (motive := fun j =>
      TreeSequenceInitialSegment (HB.stage j) B)
      (by rw [HB.terminalStage]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      (fun i hi => trans (HB.nested i) hi) j
  have terminalTree : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    exact corr.terminalData.1
  have terminalStored : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = TashkinovStoredColors EB.series.data
        (Fin.last EB.rounds) := by
    exact corr.terminalData.2.2
  exact @helper_continuation_5341 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hpathLower)
      (@P) (@alpha) (@hp) (@hpUpper) (@htail) (@trans) (@hlenT) (@hBlength) (@hXlength) (@hBT)
      (@hXB) (@hTnX) (@consecutive) (@hyf) (@S) (@hSBlen) (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz)
      (@hzy) (@hzX) (@hab) (@fixed) (@missingFixed) (@fixedB) (@missingTree) (@minusEq)
      (@lastPositive) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@HB)
      (@hcountB) (@hstagesB) (@goodB) (@coreBX) (@closureBX) (@corr) (@hmaximum) (@bs) (@hcore)
      (@hpe) (@hclosure) (@baseStageK) (@terminalStageK) (@nestedK) (@strictK) (@coreInsideK)
      (@positiveK) (@increasingK) (@dividerStageK) (@starredEq) (@stageBX) (@starBX) (@allStageB)
      (@terminalTree) (@terminalStored)

private theorem helper_shortening_124.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (2 : ℕ) ≤
        HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C → HierarchyFullTailLength C - (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper hlast
  classical
  open scoped Sym2 in
    obtain ⟨P, alpha, haB, haT⟩ := (Finset.mem_filter.mp hlast).2
    let old := P.counterexample
    let H := old.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let n := Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let mu := P.coloring
    have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      apply helper_sameLast_4591
    have hAold : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A :=
      sameLast _ _ _ _ P.sameGood.1.2.1 P.sameGood.1.2.2.1 P.sameGood.1.1
    have hp : HierarchyPathNumber H = HierarchyPathNumber C.hierarchy := by
      unfold HierarchyPathNumber
      dsimp only
      rw [hAold]
    have hpLower : 2 ≤ HierarchyPathNumber H := by rw [hp]; exact hpathLower
    have hpUpper : HierarchyPathNumber H < T.length - A.length := by
      exact helper_hpUpper_1652 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@hpathUpper) (@P) (@hAold) (@hp)
    have htail : 2 ≤ T.length - A.length :=
      HierarchyCounterexampleTailAtLeastTwo G k e0 P.corresponding.replacementInput
        T mu P.corresponding.replacementETT P.replacementBase old
        P.minimumContext.proper P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      exact helper_trans_1665 (@G) (@e0) (@hXY) (@hYZ)
    have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
        (i : Fin (H.dividerCount + 2)), i.val ≤ j →
        TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
      intro j hj i hi
      exact H.stageInitialSegmentOfLE i ⟨j, hj⟩ hi
    have starNext (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H j) (H.stage j.succ) := by
      refine Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) j
    have hAT : TreeSequenceInitialSegment A T := by
      have hh := starNext (Fin.last H.dividerCount)
      simpa only [Fin.succ_last, H.terminalStage] using hh
    have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
      exact helper_hTnCore_1684 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
    have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
      apply helper_coreA_200 <;> assumption
    have hTnA := trans hTnCore coreA
    have hlenT : 3 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    let X := TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
    have hBlength : B.length = T.length - 1 := rfl
    have hXlength : X.length = T.length - 2 := rfl
    have hBT : TreeSequenceInitialSegment B T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have hXT : TreeSequenceInitialSegment X T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have common {S U W : TreeSequence G e0}
        (hSW : TreeSequenceInitialSegment S W)
        (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
        TreeSequenceInitialSegment S U := by
      exact hUW.of_common_extension hSW hlen
    have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by omega)
    have hXB : TreeSequenceInitialSegment X B := common hXT hBT (by omega)
    have hTnX := trans hTnA hAX
    have hAB := trans hAX hXB
    have hfull : HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1) = B := by
      exact helper_hfull_1715 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@hAold) (@htail) (@hlenT)
    have halphaB : alpha ∈ MissingColors G mu (B.vertex (Fin.last B.length)) := by
      rw [hfull] at haB
      exact haB
    let r : Fin T.length := ⟨T.length - 1, by omega⟩
    let f := T.edge r
    let y := B.vertex (Fin.last B.length)
    let w := T.vertex (Fin.last T.length)
    have hy : T.vertex r.castSucc = y := by rfl
    have hw : T.vertex r.succ = w := by
      apply congrArg T.vertex
      apply Fin.ext
      dsimp [r]
      omega
    have consecutive (t : Fin T.length)
        (ht : A.length + HierarchyPathNumber H ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      exact helper_consecutive_852 G k e0 input T phi ett base C ctx P hpUpper hlenT t ht
    have hends : G.ends f = s(y, w) :=
      (consecutive r (by dsimp [r]; omega)).trans (by rw [hy, hw])
    have hyf : Incident G y f := by rw [Incident, hends]; exact Sym2.mem_mk_left _ _
    have hwf : Incident G w f := by rw [Incident, hends]; exact Sym2.mem_mk_right _ _
    have hsource : ∃ S : TreeSequence G e0,
        S.length ≤ B.length ∧ TashkinovAugmentationSequence mu S T := by
      exact helper_hsource_1746 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@hlenT) (@hBlength) (@hXlength) (@hTnX)
    obtain ⟨S, hSBlen, hseq⟩ := hsource
    obtain ⟨hlen, hpre, beta, hbetaColor, hbetaMissing⟩ :=
      (TashkinovAugmentationSequencePosition mu S T hseq r
        (by simpa only [B, TreeSequencePrefix, r] using hSBlen)).1
    have hbetaF : mu f = some beta := by
      convert hbetaColor using 1
      congr 2
    have hbetaB : beta ∈ TreeMissingColors mu B := hbetaMissing
    obtain ⟨z, hzB, hbetaz⟩ := Finset.mem_biUnion.mp hbetaB
    have hzy : z ≠ y := by
      exact helper_hzy_1763 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@hlenT) (@hyf) (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz)
    have hzX : z ∈ TreeSequenceVertexSet X := by
      apply helper_hzX_1770 <;> assumption
    have hab : alpha ≠ beta := by
      intro he
      have halphaPresent : alpha ∈ PresentColors G mu y := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hyf, by rw [he]; exact hbetaF⟩
      exact (Finset.mem_sdiff.mp halphaB).2 halphaPresent
    let sigma : PartialEdgeColoring E k := fun e => if e = f then some alpha else mu e
    have fixed (e : E) (hef : e ≠ f) : sigma e = mu e := by simp [sigma, hef]
    have hsproper : IsProperEdgeColoring G sigma := by
      exact SharedFacts.ShorteningProofs.properRecoloring P.minimumContext.proper
        f alpha y w hends halphaB haT (by simp [sigma]) fixed
    have hfe0 : f ≠ e0 := by
      apply helper_hfe0_1788 <;> assumption
    have hsone : IsOneEdgeUncolored sigma e0 := by
      exact helper_hsone_1794 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@hlenT) (@fixed) (@hfe0)
    have noInc (v : V) (hv : v ∈ TreeSequenceVertexSet X) : ¬ Incident G v f := by
      apply helper_noInc_930 <;> assumption
    have incidentFixed (e : E) (he : TreeIncidentEdge X e) : sigma e = mu e := by
      apply fixed
      intro hef
      obtain ⟨v, hv, hi⟩ := he
      exact noInc v hv (hef ▸ hi)
    have missingFixed (v : V) (hv : v ∈ TreeSequenceVertexSet X) :
        MissingColors G sigma v = MissingColors G mu v := by
      apply helper_missingFixed_1810 <;> assumption
    have fixedB (t : Fin B.length) : sigma (B.edge t) = mu (B.edge t) := by
      apply helper_fixedB_2088 <;> assumption
    have stable : StableColoring Tn
        (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
        (P.corresponding.replacementETT.series.data.coloring n) sigma := by
      exact helper_stable_2096 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@hlenT) (@hTnX) (@incidentFixed) (@missingFixed)
    have hrouteB :
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
            P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (edge : E) (seed : TreeSequence G e0),
            P.corresponding.replacementETT.series.data.connectingEdges n = {edge} ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧
            TashkinovAugmentationSequence sigma seed B) := by
      apply helper_hrouteB_979 <;> assumption
    have missingTree (U : TreeSequence G e0)
        (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) :
        TreeMissingColors sigma U = TreeMissingColors mu U := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => missingFixed v (hUX hv))
    exact @helper_continuation_5697 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hpathLower) (@P) (@alpha) (@hp) (@hpUpper) (@htail) (@trans) (@chain) (@coreA) (@hTnA)
        (@hlenT) (@hBlength) (@hXlength) (@hBT) (@hAX) (@hXB) (@hTnX) (@hAB) (@consecutive)
        (@hends) (@hyf) (@S) (@hSBlen) (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz) (@hzy) (@hzX)
        (@hab) (@fixed) (@hsproper) (@hsone) (@incidentFixed) (@missingFixed) (@fixedB) (@stable)
        (@hrouteB) (@missingTree)
private theorem helper_branch_1318.{u_1, u_2} :
    helperBranch1318Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A hlen B vertexMem firstAt stageSwitch
      gammaTransport gammaChoice m P alpha haLast hm hmT X hAX hXB hAXlt jm jnext tnext haM theta
      htheta nextMember excNext excM avoidM hAlphaStored
  obtain ⟨gamma, hgamma, hgap⟩ := gammaChoice P alpha hAlphaStored (T.edge tnext)
  obtain ⟨P1, hmissing1, hfixed1, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
    gamma alpha alpha hAlphaStored hgamma
    (by rw [firstAt P alpha jm haM]; dsimp [jm, X, TreeSequencePrefix]; omega)
    jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
    haM (Or.inr haLast) (avoidM P alpha gamma hAlphaStored hgamma haM hgap)
    (excM P alpha haM)
  have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1
      haLast
  have haM1 : alpha ∈ MissingColors G P1.coloring (B.vertex jm) := by
    rw [hmissing1 _ (vertexMem B jm)]; exact haM
  have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
    rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
  obtain ⟨hAlphaStored1, heqGamma⟩ := gammaTransport P P1 alpha hAlphaStored
  have hgamma1 : gamma ∈ P1.counterexample.good.gamma
      (Fin.last P1.counterexample.hierarchy.dividerCount) alpha := by
    rw [← heqGamma]; exact hgamma
  have hgap1 : P1.coloring (T.edge tnext) ≠ some gamma := by
    rw [hfixed1 tnext (by dsimp [tnext]; omega)
      (by dsimp [tnext, X, TreeSequencePrefix]; omega)]
    exact hgap
  obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
    gamma theta alpha hAlphaStored1 hgamma1
    (by rw [firstAt P1 alpha jm haM1]; dsimp [jm, X, TreeSequencePrefix]; omega)
    jnext (by dsimp [jnext]; omega) (by rfl)
    htheta1 (Or.inl hgLast) (avoidM P1 alpha gamma hAlphaStored1 hgamma1 haM1 hgap1)
    (excNext P1 theta htheta1)
  exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
    (hterminal2 hgLast)

private theorem helper_branch_1872.{u_1, u_2} :
    helperBranch1872Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A hlen B vertexMem firstAt stageSwitch
      gammaTransport gammaChoice m P alpha haLast hm hmT X hAX hXB hAXlt jm jnext tnext haM theta
      htheta nextMember excNext excM avoidNext hThetaStored
  obtain ⟨gamma, hgamma, _⟩ := gammaChoice P theta hThetaStored (T.edge tnext)
  obtain ⟨P1, hmissing1, _, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
    gamma alpha theta hThetaStored hgamma
    (by rw [firstAt P theta jnext htheta]; exact le_rfl)
    jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
    haM (Or.inr haLast) (avoidNext P theta gamma hThetaStored hgamma htheta)
    (excM P alpha haM)
  have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1
      haLast
  have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
    rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
  obtain ⟨hThetaStored1, heqGamma⟩ := gammaTransport P P1 theta hThetaStored
  have hgamma1 : gamma ∈ P1.counterexample.good.gamma
      (Fin.last P1.counterexample.hierarchy.dividerCount) theta := by
    rw [← heqGamma]; exact hgamma
  obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
    gamma theta theta hThetaStored1 hgamma1
    (by rw [firstAt P1 theta jnext htheta1]; exact le_rfl)
    jnext (by dsimp [jnext]; omega) (by rfl)
    htheta1 (Or.inl hgLast) (avoidNext P1 theta gamma hThetaStored1 hgamma1 htheta1)
    (excNext P1 theta htheta1)
  exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
    (hterminal2 hgLast)

private theorem helper_continuation_2372.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦
    by omega
    ); TreeSequenceInitialSegment B T → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    ∀ (m : ℕ) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
    ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦
    by
          omega
    );
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let jnext : Fin (B.length + (1 : ℕ)) := (⟨A.length + (m + (1 : ℕ)), id
        (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 :
        ℕ)) ↦
    by
              omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext), (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∈ MissingColors G S.coloring (B.vertex jnext), c ∈ MissingColors G S.coloring (T.vertex
        (Fin.last T.length)) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx) → alpha ∉ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount) → theta ∉ HierarchyStoredColorsAt
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount) → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → P.coloring (T.edge t) ≠ some
        alpha) → alpha ≠ theta → (↑(HierarchyFirstMissingPosition P.coloring T alpha) : ℕ) = (↑jm
        : ℕ) → (↑(HierarchyFirstMissingPosition P.coloring T theta) : ℕ) = (↑jnext : ℕ) →
        TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition P.coloring T alpha)) (T.vertex
        (HierarchyFirstMissingPosition P.coloring T theta)) → ColoredVertexSetElementary G
        P.coloring (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - (1 : ℕ)))) → alpha ∈ TreeMissingColors
        P.coloring (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength
        P.counterexample - (1 : ℕ))) ∧ theta ∈ TreeMissingColors P.coloring
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ))) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G P.coloring alpha theta
        (Sum.inl (T.vertex (Fin.last T.length)))) x = MissingColors G P.coloring x) →
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha theta (Sum.inl
        (T.vertex (Fin.last T.length))); (
    ∀ v ∈ TreeSequenceVertexSet A, TreeVertexOrder T v (T.vertex (HierarchyFirstMissingPosition
        P.coloring T alpha))) → m + (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx trans A starEq hlen B hBT vertexMem m P
      alpha haLast hm hmT X jm jnext theta htheta nextMember hAlphaStored hThetaStored haUnused
      hne iaEq ibEq hordered hprefixP hmissingP hmissing sigma hprecedes
  have hunusedBetween : alpha ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      (HierarchyFirstMissingPosition P.coloring T alpha).val ≤ t.val ∧
      t.val < (HierarchyFirstMissingPosition P.coloring T theta).val ∧
      P.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    rw [iaEq] at hlo
    rw [ibEq] at hhi
    exact haUnused t (by dsimp [jm] at hlo; omega) hhi hc
  obtain ⟨_, _, _, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
    StableChangeCaseThree G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
      P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality hprefixP
      P.minimumContext.largeMissingSet alpha theta hne hmissingP _ sigma rfl
      (by rw [starEq P]; exact hprecedes) hordered
      ⟨hAlphaStored, hThetaStored⟩ hunusedBetween
  have hthetaLast : theta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    (TwoColorComponentSwapMissingBehavior G P.coloring alpha theta hne
      P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.1 _ (by rfl) haLast
  have hthetaNext : theta ∈ MissingColors G sigma (B.vertex jnext) := by
    rw [hmissing _ (vertexMem B jnext)]
    exact htheta
  have hnot : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    intro he
    exact Finset.disjoint_left.mp (he
      (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jnext))
      (vertexMem T (Fin.last T.length)) (by
        intro hh
        have hh := T.vertex_injective ((hBT.2.1 jnext).trans hh)
        have hh := congrArg Fin.val hh; dsimp [jnext] at hh; omega)) hthetaNext hthetaLast
  let CS : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnot }
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs CS hsameGood
  exact nextMember S theta (by rw [hS]; exact hthetaNext) (by rw [hS]; exact hthetaLast)

private theorem helper_branch_1894.{u_1, u_2} :
    helperBranch1894Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx componentData trans A starEq hAT hlen B hBT
      fullB elementary vertexMem firstAt outsideA notRaw m P alpha ha haLast hm hmT X jm jnext
      haM theta htheta nextMember excM hAlphaStored hThetaStored
  have haOutside := outsideA P alpha jm (by dsimp [jm]; omega) haM
  have hthetaOutside := outsideA P theta jnext (by dsimp [jnext]; omega) htheta
  have haRaw := notRaw P alpha haOutside hAlphaStored
  have hthetaRaw := notRaw P theta hthetaOutside hThetaStored
  have haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      P.coloring (T.edge t) ≠ some alpha := by
    intro t hlo hhi hc
    exact haRaw (excM P alpha haM t hlo hhi hc).2
  have iaEq := firstAt P alpha jm haM
  have ibEq := firstAt P theta jnext htheta
  obtain ⟨hne, hordered, hprefixP, hmissingP, hmissing, hprecedes⟩ :=
    P.minimumContext.tailSwapData A B hAT hBT (starEq P) (fullB P) (elementary P)
      vertexMem componentData alpha theta jm jnext
      (by dsimp [jm]; omega) (by dsimp [jm, jnext]; omega)
      (by dsimp [jnext]; omega) haM htheta haLast hAlphaStored hThetaStored haRaw hthetaRaw
      iaEq ibEq haUnused
  exact @helper_continuation_2372 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx trans starEq hlen hBT vertexMem m P alpha haLast hm hmT theta
      htheta nextMember hAlphaStored hThetaStored haUnused hne iaEq ibEq hordered hprefixP
      hmissingP hmissing hprecedes
private theorem helper_branch_1346.{u_1, u_2} :
    helperBranch1346Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx componentData trans A starEq hAT hlen B hBT
      fullB elementary vertexMem firstAt stageSwitch gammaTransport outsideA notRaw gammaChoice m
      P alpha ha haLast hm hmT X hAX hXB hAXlt jm jnext tnext haM theta htheta nextMember excNext
      excM avoidNext hAlphaStored
  by_cases hThetaStored : theta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_1872 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hlen vertexMem firstAt stageSwitch gammaTransport gammaChoice m
      P alpha haLast hm hmT hAX hXB hAXlt haM theta htheta nextMember excNext excM avoidNext
      hThetaStored
  · exact @helper_branch_1894 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx componentData trans starEq hAT hlen hBT fullB elementary
      vertexMem firstAt outsideA notRaw m P alpha ha haLast hm hmT haM theta htheta nextMember
      excM hAlphaStored hThetaStored
private theorem helper_excM_2308.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦
    by omega
    ); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ), (1 : ℕ) ≤
        j → j < T.length - A.length →
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds)) → (
    ∀ (t : Fin T.length), A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ) → G.ends (T.edge
        t) = s(T.vertex t.castSucc, T.vertex t.succ)) →
    ∀ (m : ℕ), HierarchyPathNumber C.hierarchy ≤ m →
    ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦
    by
          omega
    );
    let Y : TreeSequence G e0 := TreeSequencePrefix T (A.length + m) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + m) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + m ≤ T.length) ↦
    by omega
    );
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let _ : Fin T.length := (⟨A.length + m, Decidable.byContradiction fun (a : ¬A.length + m <
        T.length) ↦
    by omega
    ⟩ : Fin T.length); HierarchyFullTailPrefix C m = Y → Y.vertex (Fin.last Y.length) = B.vertex
        jm →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A hAT hlen B tailException consecutive m
      hmLower hm hmT X Y jm tnext hfullY hYvertex R b hb t hlo hhi hcol
  by_cases ht : t.val < A.length + m
  · exact tailException R m (by omega) (by have := hAT.1; omega) b
      (by rw [hfullY, hYvertex]; exact hb) t hlo ht hcol
  · have htEq : t = tnext := Fin.ext
      (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
    subst t
    have he := consecutive tnext (by dsimp [tnext]; omega)
    have hv : T.vertex tnext.castSucc = B.vertex jm := rfl
    have hi : Incident G (B.vertex jm) (T.edge tnext) := by
      rw [Incident, he, hv]
      exact Sym2.mem_mk_left _ _
    exact ((Finset.mem_sdiff.mp hb).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge tnext, hi, hcol⟩)).elim

private theorem helper_advance_1257.{u_1, u_2} :
    helperAdvance1257Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing
      componentData trans common A starEq hAT hlen B hBT fullB elementary vertexMem firstAt
      stageSwitch gammaTransport gammaUnused outsideA notRaw tailException consecutive
      gammaChoice m hmLower hmUpper P alpha ha haLast
  have hm : 2 ≤ m := le_trans hpathLower hmLower
  have hmT : A.length + (m + 1) < T.length := by
    change m < (T.length - A.length) - 1 at hmUpper
    have := hAT.1
    omega
  let X := TreeSequencePrefix T (A.length + (m + 1)) (by have := A.positive; omega) (by omega)
  let Y := TreeSequencePrefix T (A.length + m) (by have := A.positive; omega) (by omega)
  have hXT : TreeSequenceInitialSegment X T := ⟨by exact le_of_lt hmT, fun _ => rfl, fun _ => rfl⟩
  have hAX : TreeSequenceInitialSegment A X := common hAT hXT
      (by dsimp [X, TreeSequencePrefix]; omega)
  have hXB : TreeSequenceInitialSegment X B :=
    common hXT hBT (by dsimp [X, B, TreeSequencePrefix]; omega)
  have hAXlt : A.length < X.length := by dsimp [X, TreeSequencePrefix]; omega
  let jm : Fin (B.length + 1) := ⟨A.length + m, by dsimp [B, TreeSequencePrefix]; omega⟩
  let jnext : Fin (B.length + 1) := ⟨A.length + (m + 1), by dsimp [B, TreeSequencePrefix]; omega⟩
  let tnext : Fin T.length := ⟨A.length + m, by omega⟩
  have hfullY : HierarchyFullTailPrefix C m = Y := by
    have hn : min (A.length + m) T.length = A.length + m := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + m) T.length) _ _ = Y
    simp only [hn]
    rfl
  have hfullX : HierarchyFullTailPrefix C (m + 1) = X := by
    have hn : min (A.length + (m + 1)) T.length = A.length + (m + 1) := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + (m + 1)) T.length) _ _ = X
    simp only [hn]
    rfl
  have hYvertex : Y.vertex (Fin.last Y.length) = B.vertex jm := rfl
  have hXvertex : X.vertex (Fin.last X.length) = B.vertex jnext := rfl
  have haM : alpha ∈ MissingColors G P.coloring (B.vertex jm) := by
    rw [hfullY, hYvertex] at ha
    exact ha
  obtain ⟨theta, htheta⟩ := hvertexMissing P.coloring P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored (B.vertex jnext)
  have nextMember (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (hc : c ∈ MissingColors G S.coloring (B.vertex jnext))
      (hcLast : c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) :
      m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, S, c, ?_, hcLast⟩
    rw [hfullX, hXvertex]
    exact hc
  have excNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jnext))
      (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
      (hcol : R.coloring (T.edge t) = some b) :
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    apply tailException R (m + 1) (by omega) (by have := hAT.1; omega) b
      (by rw [hfullX, hXvertex]; exact hb) t hlo
      (by exact hhi) hcol
  have excM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jm))
      (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
      (hcol : R.coloring (T.edge t) = some b) :
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    exact helper_excM_2308 G k e0 input T phi ett base C ctx hAT hlen tailException consecutive m
        hmLower hm hmT hfullY hYvertex R b hb t hlo hhi hcol
  have avoidNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jnext)) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    apply gammaUnused R eta a heta ha t hlo
    rw [firstAt R eta jnext he]
    exact hhi
  have avoidM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jm))
      (hgap : R.coloring (T.edge tnext) ≠ some a) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    by_cases ht : t.val < A.length + m
    · apply gammaUnused R eta a heta ha t hlo
      rw [firstAt R eta jm he]
      exact ht
    · have htEq : t = tnext := Fin.ext
        (by change t.val < A.length + (m + 1) at hhi; dsimp [tnext]; omega)
      simpa only [htEq] using hgap
  by_cases hAlphaStored : alpha ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount)
  · exact @helper_branch_1318 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hlen vertexMem firstAt stageSwitch gammaTransport gammaChoice m
      P alpha haLast hm hmT hAX hXB hAXlt haM theta htheta nextMember excNext excM avoidM
      hAlphaStored
  · exact @helper_branch_1346 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx componentData trans starEq hAT hlen hBT fullB elementary
      vertexMem firstAt stageSwitch gammaTransport outsideA notRaw gammaChoice m P alpha ha
      haLast hm hmT hAX hXB hAXlt haM theta htheta nextMember excNext excM avoidNext hAlphaStored
private theorem helper_outsideA_2628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦
    by omega
    ); TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) → (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (B.length + (1 : ℕ))), A.length < (↑j : ℕ) → c ∈ MissingColors G R.coloring (B.vertex
        j) → c ∉ TreeMissingColors R.coloring A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx trans A hAT hlen B hBT hAB elementary
      vertexMem R c j hj hc
  clear * - R c j hj hc hAT hBT hAB elementary vertexMem
  rintro hm
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a, ha⟩ : ∃ a, A.vertex a = v := by simpa [TreeSequenceVertexSet] using hv
  have hne : v ≠ B.vertex j := by
    intro he
    have hh := T.vertex_injective ((hAT.2.1 a).trans
      (ha.trans (he.trans (hBT.2.1 j).symm)))
    have hh := congrArg Fin.val hh
    have := a.isLt
    change a.val = j.val at hh
    omega
  exact Finset.disjoint_left.mp (elementary R
    (TreeSequenceInitialSegmentVertexSetSubset hAB hv) (vertexMem B j) hne) hcv hc

private theorem helper_consecutive_2671.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ) → G.ends (T.edge
        t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpathUpper A t ht
  let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  have hp : HierarchyPathNumber C.hierarchy =
      (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
  have hn : candidates.Nonempty := by
    by_contra hn
    rw [dite_eq_right hn] at hp
    have hu : HierarchyPathNumber C.hierarchy < T.length - A.length := hpathUpper
    omega
  have hm : candidates.min' hn = HierarchyPathNumber C.hierarchy := by
    simpa only [dite_eq_left hn] using hp.symm
  have hh := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  rw [hm] at hh
  exact hh t ht

private theorem helper_hAT_3385.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C A
  have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
        (C.hierarchy.stage j.succ) :=
    Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
  simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
    starNext (Fin.last C.hierarchy.dividerCount)

private theorem helper_fullB_3407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → (3 : ℕ) ≤ T.length - A.length →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := TreeSequence.positive T
          omega
    ) (
    by
          have := TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx A starEq htail hlen B R
  have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [starEq R]
    omega
  simp only [HierarchyFullTailPrefix, hn]
  rfl

private theorem helper_elementary_3419.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (by
          have := TreeSequence.positive T
          omega)
        (by
          have := TreeSequence.positive T
          omega);
    (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
          B) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hlen B fullB R
  have h : ColoredVertexSetElementary G R.coloring
    (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - 1))) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0
      R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
      R.replacementBase R.counterexample R.minimumContext.proper
      R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
      R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
      R.minimumContext.largeMissingSet
  intro u hu v hv hne
  exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne

theorem HierarchySituationThreeEligibleIndexBound {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty) :
    ∀ i ∈ HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx,
      i < HierarchyPathNumber C.hierarchy := by
  classical
  have shortening (hlast : HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx) : False := by
    exact helper_shortening_124 G k e0 input T phi ett base C ctx hpathLower hpathUpper hlast
  classical
  have componentData (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hproper : IsProperEdgeColoring G psi)
      (B : Finset V) (helem : ColoredVertexSetElementary G psi B)
      (u v w : V) (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v)
      (hwu : w ≠ u) (hwv : w ≠ v)
      (hau : a ∈ MissingColors G psi u) (hbv : b ∈ MissingColors G psi v)
      (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w)
      (hsame : TwoColorComponent G psi a b (Sum.inl u) =
        TwoColorComponent G psi a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G psi a b (Sum.inl w))
          (TwoColorComponent G psi a b (Sum.inl u)) ∧
        TwoColorPathComponent G psi a b (Sum.inl w) ∧
        (∀ x ∈ B,
          MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
            MissingColors G psi x) := by
    exact P2905_T2_ElementaryTerminalComponent G psi a b hne hproper
      B helem u v w hu hv hwu hwv hau hbv hw hsame
  classical
  open scoped Sym2 in
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      exact SharedFacts.ShorteningTransport.trans (@G) (@e0) (@hXY) (@hYZ)
    have common {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z)
        (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
        TreeSequenceInitialSegment X Y := by
      exact hYZ.of_common_extension hXZ hXY
    have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      apply SharedFacts.OutsideAdvancement.sameLast
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
      (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
    have hAT : TreeSequenceInitialSegment A T := by
      exact helper_hAT_3385 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
    have htail : 3 ≤ T.length - A.length := by
      change HierarchyPathNumber C.hierarchy < T.length - A.length at hpathUpper
      omega
    have hlen : 4 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    have hBT : TreeSequenceInitialSegment B T := ⟨by dsimp [B, TreeSequencePrefix]; omega,
      fun _ => rfl, fun _ => rfl⟩
    have hAB : TreeSequenceInitialSegment A B :=
      common hAT hBT (by dsimp [B, TreeSequencePrefix]; omega)
    have fullEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) : HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j := by
      unfold HierarchyFullTailPrefix
      dsimp only
      simp only [starEq R]
      rfl
    have fullB (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyFullTailPrefix R.counterexample
          (HierarchyFullTailLength R.counterexample - 1) = B := by
      exact helper_fullB_3407 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@starEq) (@htail) (@hlen) (@R)
    have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
      exact helper_elementary_3419 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@hlen) (@fullB) (@R)
    have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
        U.vertex j ∈ TreeSequenceVertexSet U := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
        (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
        HierarchyFirstMissingPosition psi T c ≤ j := by
      exact SharedFacts.OutsideAdvancement.firstMissingPositionUpperBound (@G) (@k) (@e0) (@T)
          (@psi) (@c) (@j) (@hj)
    have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
        c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
      exact TreeSequenceFirstMissingPositionMem hlt
    have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1))
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by
      exact TreeSequenceFirstMissingPositionEqCast hBT (elementary R) hc
    have stageSwitch := P2963_T1_TerminalKempeStageSwitch G k e0 input T phi ett base C ctx
      A B (by omega) rfl rfl
    have lastData (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
          HierarchyStoredColorsAt R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount) ∧
        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
          C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
            R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta := by
      exact SharedFacts.OutsideAdvancement.lastData (@G) (@k) (@e0) (@input) (@T) (@phi)
          (@ett) (@base) (@C) (@ctx)
          (@R)
    have gammaTransport
        (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        eta ∈ HierarchyStoredColorsAt S.counterexample.hierarchy
          (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
          S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
      apply SharedFacts.OutsideAdvancement.gammaTransport <;> assumption
    have gammaUnused (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta a : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount))
        (ha : a ∈ R.counterexample.good.gamma
          (Fin.last R.counterexample.hierarchy.dividerCount) eta)
        (t : Fin T.length) (hlo : A.length ≤ t.val)
        (hhi : t.val < (HierarchyFirstMissingPosition R.coloring T eta).val) :
        R.coloring (T.edge t) ≠ some a := by
      exact SharedFacts.OutsideAdvancement.gammaUnused (@G) (@k) (@e0) (@input) (@T) (@phi)
          (@ett) (@base) (@C)
          (@ctx) (@starEq) (@R) (@eta) (@a) (@heta) (@ha) (@t) (@hlo) (@hhi)
    have outsideA (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (j : Fin (B.length + 1)) (hj : A.length < j.val)
        (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
        c ∉ TreeMissingColors R.coloring A := by
      apply helper_outsideA_2628 <;> assumption
    have notRaw (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (c : Fin k) (hcA : c ∉ TreeMissingColors R.coloring A)
        (hcD : c ∉ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) :
        c ∉ TashkinovStoredColors R.corresponding.replacementETT.series.data
          (Fin.last R.corresponding.replacementETT.rounds) := by
      exact SharedFacts.OutsideAdvancement.notRaw (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
          (@base) (@C) (@ctx)
          (@starEq) (@R) (@c) (@hcA) (@hcD)
    have tailException (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) (hj : 1 ≤ j) (hjlt : j < T.length - A.length)
        (c : Fin k)
        (hc : c ∈ MissingColors G R.coloring
          ((HierarchyFullTailPrefix C j).vertex (Fin.last (HierarchyFullTailPrefix C j).length)))
        (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < A.length + j)
        (hcol : R.coloring (T.edge t) = some c) :
        TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
          c ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
            (Fin.last R.corresponding.replacementETT.rounds) := by
      apply SharedFacts.InsideAdvancement.tailException <;> assumption
    have consecutive (t : Fin T.length)
        (ht : A.length + HierarchyPathNumber C.hierarchy ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      exact helper_consecutive_2671 G k e0 input T phi ett base C hpathUpper t ht
    have gammaChoice (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (eta : Fin k)
        (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount)) (f : E) :
        ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
          R.coloring f ≠ some a := by
      apply SharedFacts.OutsideAdvancement.gammaChoice; assumption
    have advance (m : ℕ) (hmLower : HierarchyPathNumber C.hierarchy ≤ m)
        (hmUpper : m < HierarchyFullTailLength C - 1)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (alpha : Fin k)
        (ha : alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C m).vertex (Fin.last (HierarchyFullTailPrefix C m).length)))
        (haLast : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
        m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
      exact @helper_advance_1257 V E inferInstance inferInstance inferInstance inferInstance G k
          e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing componentData trans
          common starEq hAT hlen hBT fullB elementary vertexMem firstAt stageSwitch
          gammaTransport gammaUnused outsideA notRaw tailException consecutive gammaChoice m
          hmLower hmUpper P alpha ha haLast
    intro i hi
    by_contra hn
    let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
    have hI : I.Nonempty := ⟨i, hi⟩
    let m := I.max' hI
    have hmI : m ∈ I := Finset.max'_mem I hI
    have him : i ≤ m := Finset.le_max' I i hi
    have hmBounds : 1 ≤ m ∧ m ≤ HierarchyFullTailLength C - 1 :=
      Finset.mem_Icc.mp (Finset.mem_filter.mp hmI).1
    obtain ⟨P, alpha, ha, haLast⟩ := (Finset.mem_filter.mp hmI).2
    by_cases hlast : m = HierarchyFullTailLength C - 1
    · exact shortening (hlast ▸ hmI)
    · have hnext := advance m (by omega) (by omega) P alpha ha haLast
      have hh : m + 1 ≤ m := Finset.le_max' I (m + 1) hnext
      omega

end GoldbergSeymour

end
