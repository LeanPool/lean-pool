/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseThreeOne.Preparation1

/-!
# HierarchySituationTwoSubcaseThreeOne: supporting constructions, part 2

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchySituationTwoSubcaseThreeOnePreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation3712Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
   let alpha : Fin k := D.alpha;
   let theta : Fin k := D.theta;
   let lastIndex : Fin T.length := D.lastEdgeIndex;
   let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
   let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let ell : ℕ := HierarchyFullTailLength C;
   let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
   let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   phi (T.edge lastIndex) = some theta →
    alpha ∈ MissingColors G phi (T.vertex endIndex) →
     alpha ∈ TreeMissingColors phi B →
      (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some alpha) →
       (↑lastIndex : ℕ) + (1 : ℕ) = T.length →
        (↑penIndex : ℕ) + (1 : ℕ) = T.length →
         (↑endIndex : ℕ) = T.length →
          (have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
           have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
           have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
           ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
             TashkinovAugmentationSequence phi Tn T ∨
            (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
             ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
               TreeSequenceAdjoinEdge Tn f seed ∧
                TreeIncidentEdge Tn f ∧
                 (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
                  TashkinovAugmentationSequence phi seed T) →
           (∃ eta ∈ HierarchyStoredColorsAt H q,
             eta ∈ MissingColors G phi (T.vertex penIndex) ∧ theta ∈ C.good.gamma q eta) →
            False

theorem helper_continuation_3712.{u_1, u_2} :
    helperContinuation3712Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastColor alphaTerminal alphaBefore alphaUnused lastPosition
      penPosition endPosition oldRoute h_exception
  rcases h_exception with ⟨eta, hetaStored, hetaMissing, hthetaGamma⟩
  have hTailAtLeast : 2 ≤ ell := D.tailAtLeastTwo
  have hellOuter : ell = T.length - A.length := rfl
  have hBLouter : B.length + 2 = T.length := by
    simp only [B, HierarchyFullTailPrefix, TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
    rw [← hellOuter]
    omega
  have hPLouter : Bplus.length + 1 = T.length := by
    simp only [Bplus, HierarchyFullTailPrefix, TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    rw [← hellOuter]
    omega
  have hBTouter : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBplusTouter : TreeSequenceInitialSegment Bplus T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBBplusOuter : TreeSequenceInitialSegment B Bplus := by
    exact helper_hBBplusOuter_953 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@penPosition) (@endPosition) (@hBLouter) (@hPLouter)
  have hATouter : TreeSequenceInitialSegment A T := by
    exact helper_hATouter_959 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
  have hABouter : TreeSequenceInitialSegment A B := by
    exact helper_hABouter_980 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@penPosition)
        (@endPosition) (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter) (@hATouter)
  have hABplusouter : TreeSequenceInitialSegment A Bplus := by
    exact helper_hABplusouter_986 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@penPosition) (@endPosition) (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter)
        (@hATouter)
  have hElemOuter : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have missingMonoOuter {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors phi X ⊆ TreeMissingColors phi Y :=
    Finset.biUnion_subset_biUnion_of_subset_left (MissingColors G phi)
      (TreeSequenceInitialSegmentVertexSetSubset hXY)
  have hAlphaWitness : ∃ v ∈ TreeSequenceVertexSet B,
      alpha ∈ MissingColors G phi v := by
    exact Finset.mem_biUnion.mp alphaBefore
  obtain ⟨vAlpha, hvAlpha, hAlphaAt⟩ := hAlphaWitness
  have vertexMemOuter (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
      X.vertex i ∈ TreeSequenceVertexSet X :=
    (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
  have firstMissingOuter (X : TreeSequence G e0) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi X) :
      c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
    exact helper_firstMissingOuter_1008 (@G) (@k) (@e0) (@phi) (@X) (@c) (@hc)
  have firstLeOuter (X : TreeSequence G e0) (c : Fin k)
      (i : Fin (X.length + 1)) (hi : c ∈ MissingColors G phi (X.vertex i)) :
      (HierarchyFirstMissingPosition phi X c).val ≤ i.val := by
    exact helper_firstLeOuter_1021 (@G) (@k) (@e0) (@phi) (@X) (@c) (@i) (@hi)
  have firstBoundByPrefix (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi X) :
      (HierarchyFirstMissingPosition phi T c).val ≤ X.length := by
    exact helper_firstBoundByPrefix_1032 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@firstLeOuter) (@X) (@hXT) (@c) (@hc)
  have hPenultimateInBplus :
      T.vertex penIndex ∈ TreeSequenceVertexSet Bplus := by
    exact helper_hPenultimateInBplus_1048 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base)
        (@C) (@ctx) (@D)
        (@penPosition) (@endPosition) (@hBLouter) (@hPLouter) (@hBplusTouter)
  have hBdef : B = HierarchyFullTailPrefix C (ell - 2) := rfl
  have hBplusDef : Bplus = HierarchyFullTailPrefix C (ell - 1) := rfl
  clear_value B Bplus
  have canonicalElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1))) :=
    hBplusDef ▸ hElemOuter
  have hAlphaEtaNe : alpha ≠ eta := by
    exact helper_hAlphaEtaNe_1071 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@B)
        (@Bplus) (@penPosition) (@endPosition) (@eta) (@hetaMissing) (@hBLouter) (@hPLouter)
        (@hBTouter) (@hBBplusOuter) (@hElemOuter) (@vAlpha) (@hvAlpha) (@hAlphaAt)
        (@hPenultimateInBplus)
  have hthetaInA : theta ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 eta hetaStored hthetaGamma
  have hetaNotA : eta ∉ TreeMissingColors phi A :=
    (Finset.mem_sdiff.mp hetaStored).2
  have hAlphaMissingBplus : alpha ∈ TreeMissingColors phi Bplus :=
    missingMonoOuter (X := B) (Y := Bplus) hBBplusOuter alphaBefore
  have hthetaMissingBplus : theta ∈ TreeMissingColors phi Bplus :=
    missingMonoOuter (X := A) (Y := Bplus) hABplusouter hthetaInA
  have canonicalMissing :
      theta ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (ell - 1)) ∧
        alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (ell - 1)) :=
    hBplusDef ▸ ⟨hthetaMissingBplus, hAlphaMissingBplus⟩
  have hetaFirst : HierarchyFirstMissingPosition phi T eta =
      penIndex := by
    exact helper_hetaFirst_1100 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@B)
        (@Bplus) (@penPosition) (@endPosition) (@eta) (@hetaMissing) (@hBLouter) (@hPLouter)
        (@hBplusTouter) (@hElemOuter) (@vertexMemOuter) (@firstMissingOuter) (@firstLeOuter)
        (@hPenultimateInBplus)
  have thetaOldAvoid : theta ∉ Finset.univ.filter (fun c =>
      ∃ r : Fin T.length, A.length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
        phi (T.edge r) = some c) := by
    exact helper_thetaOldAvoid_1134 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@eta)
        (@hetaStored) (@hthetaGamma)
  have hthetaFirstBound :
      (HierarchyFirstMissingPosition phi T theta).val ≤ A.length :=
    firstBoundByPrefix A hATouter theta hthetaInA
  have hAlphaFirstBound :
      (HierarchyFirstMissingPosition phi T alpha).val ≤ B.length :=
    firstBoundByPrefix B hBTouter alpha alphaBefore
  have hvAlphaBplus : vAlpha ∈ TreeSequenceVertexSet Bplus :=
    TreeSequenceInitialSegmentVertexSetSubset hBBplusOuter hvAlpha
  have horderedUnused :
      (theta ∉ TreeMissingColors phi A ∨ alpha ∉ TreeMissingColors phi A) →
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T theta))
          (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        theta ∉ Finset.univ.filter (fun c =>
          ∃ t : Fin T.length, A.length ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition phi T alpha).val ∧
            phi (T.edge t) = some c) := by
    exact @helper_horderedUnused_1156 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
        (@Bplus) (@alphaBefore) (@penPosition) (@eta) (@hBLouter) (@hPLouter) (@hBTouter)
        (@hATouter) (@missingMonoOuter) (@vertexMemOuter) (@firstMissingOuter) (@hthetaInA)
        (@hetaFirst) (@thetaOldAvoid) (@hthetaFirstBound) (@hAlphaFirstBound)
  have thetaAvoidsSplit : ∀ t : Fin T.length, A.length ≤ t.val →
      t.val < Bplus.length → phi (T.edge t) ≠ some theta := by
    exact helper_thetaAvoidsSplit_1203 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@penPosition) (@endPosition) (@eta) (@hBLouter) (@hPLouter) (@hetaFirst)
        (@thetaOldAvoid)
  have hthetaAlphaNe : theta ≠ alpha := by
    exact helper_hthetaAlphaNe_1213 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D) (@B)
        (@Bplus) (@lastColor) (@alphaTerminal) (@lastPosition) (@penPosition) (@endPosition) (@eta)
  have hstageTheta : theta ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta hetaStored hthetaGamma)).1
  have hThetaTn : H.dividerCount = 0 → theta ∈ TreeMissingColors phi Tn := by
    intro hz
    have hq0 : q = 0 := Fin.ext (by simp [q, hz])
    rw [hq0] at hstageTheta
    simpa [HierarchyStageMissingColors, Tn] using hstageTheta
  have hThetaTnq (hz : 0 < H.dividerCount) :
      theta ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, Nat.lt_succ_of_lt (Nat.lt_succ_self
          _)⟩) := by
    exact helper_hThetaTnq_1236 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@B)
        (@Bplus) (@eta) (@hstageTheta) (@hz)
  exact @helper_continuation_3310 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@B)
      (@Bplus) (@lastColor) (@alphaTerminal) (@alphaBefore) (@alphaUnused) (@lastPosition)
      (@penPosition) (@endPosition) (@oldRoute) (@eta) (@hetaStored) (@hetaMissing)
      (@hthetaGamma) (@hTailAtLeast) (@hellOuter) (@hBLouter) (@hPLouter) (@hBTouter)
      (@hBplusTouter) (@hBBplusOuter) (@hATouter) (@hABplusouter) (@hElemOuter)
      (@missingMonoOuter) (@vAlpha) (@vertexMemOuter) (@firstMissingOuter) (@hPenultimateInBplus)
      (@hBplusDef) (@canonicalElem) (@hAlphaEtaNe) (@hthetaInA) (@hetaNotA) (@hAlphaMissingBplus)
      (@hthetaMissingBplus) (@canonicalMissing) (@hetaFirst) (@hthetaFirstBound)
      (@hAlphaFirstBound) (@hvAlphaBplus) (@horderedUnused) (@thetaAvoidsSplit) (@hthetaAlphaNe)
      (@hThetaTn) (@hThetaTnq)
theorem helper_firstLower_5578.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    (∀ (X : TreeSequence G e0) (i : Fin (X.length + (1 : ℕ))),
        X.vertex i ∈ TreeSequenceVertexSet X) →
    (∀ (X : TreeSequence G e0),
        ∀ c ∈ TreeMissingColors phi X,
          c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))) →
    ∀ (X : TreeSequence G e0) (c : Fin k),
    ∀ t ≤ X.length,
    (∀ (i : Fin (X.length + (1 : ℕ))),
        (↑i : ℕ) < t → c ∉ MissingColors G phi (X.vertex i)) →
    t ≤ (↑(HierarchyFirstMissingPosition phi X c) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      HMinus corrStar baseStar HStar vertexMem firstMissing X c t ht hn
  as_aux_lemma =>
    by_contra hlt
    have hp : (HierarchyFirstMissingPosition phi X c).val < t := by omega
    have hm : c ∈ TreeMissingColors phi X := by
      by_contra hm
      have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
        unfold HierarchyFirstMissingPosition
        dsimp only
        rw [dite_eq_right]
        rintro ⟨i, hi⟩
        exact hm (Finset.mem_biUnion.mpr ⟨X.vertex i, vertexMem X i,
          (Finset.mem_filter.mp hi).2⟩)
      have := congrArg Fin.val he
      simp only [Fin.val_last] at this
      omega
    exact hn _ hp (firstMissing X c hm)

theorem helper_terminalData_5614.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus),
    MaximumProperty corrMinus.replacementETT →
    ∀ (baseMinus : HierarchyBase corrMinus.replacementETT phi),
    baseMinus.core = base.core →
    baseMinus.closure = base.closure →
    (↑baseMinus.supportPosition : ℕ) = (↑base.supportPosition : ℕ) →
    ∀ (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (hcountMinus : HMinus.dividerCount = C.hierarchy.dividerCount),
    (∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
        HMinus.stage j.castSucc =
          C.hierarchy.stage
            (Fin.cast
                (by
                  omega)
                j).castSucc) →
    (∀ (j : Fin HMinus.dividerCount),
        (↑(HMinus.dividerPosition j) : ℕ) =
          (↑(C.hierarchy.dividerPosition (Fin.cast hcountMinus j)) : ℕ)) →
    ∀ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    corrMinus.replacementETT.series.data.tree
          (Fin.last corrMinus.replacementETT.rounds).castSucc =
        Tn ∧
      corrMinus.replacementETT.series.data.kind (Fin.last corrMinus.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corrMinus.replacementETT.series.data
            (Fin.last corrMinus.replacementETT.rounds) =
          TashkinovStoredColors ett.series.data n := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex n Tn
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus maxMinus
      baseMinus hcoreMinus hclosureMinus hsupportMinus HMinus hcountMinus hstageMinus
      hpositionMinus corrStar baseStar HStar
  as_aux_lemma =>
    rcases corrMinus with ⟨newInput, newSeries, newETT, hr, hs, hf,
      ht, hd, he, hk, hp, ho, hstable⟩
    cases newETT with
    | mk rounds positive data above strict below generating =>
      cases hr
      have hseries : data = newSeries := eq_of_heq hs
      cases hseries
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      have hi : i.succ = Fin.last ett.rounds := Fin.ext (by
        simp [i]; have := ett.roundsPositive; omega)
      have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
        simpa [Tn, n, hi] using ht i
      refine ⟨htree, hk _, ?_⟩
      have hstored :
          TashkinovStoredColors newSeries.data (Fin.last ett.rounds) =
            TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
        unfold TashkinovStoredColors
        simp only [Fin.val_last]
        simp_rw [hd]
        rw [← hf, ← ett.generatingColoring, htree]
      simpa [n] using hstored

theorem helper_hstar_5654.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi),
    baseMinus.core = base.core →
    ∀ (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (hcountMinus : HMinus.dividerCount = C.hierarchy.dividerCount),
    (∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
        HMinus.stage j.castSucc =
          C.hierarchy.stage
            (Fin.cast
                (by
                  omega)
                j).castSucc) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        (↑j : ℕ) ≠ (0 : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
    ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
    let index :
      Fin (HMinus.dividerCount + (1 : ℕ)) → Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
      fun (j : Fin (HMinus.dividerCount + (1 : ℕ))) ↦
      Fin.cast
        (by
          omega)
        j;
    index (0 : Fin (HMinus.dividerCount + (1 : ℕ))) =
        (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))) →
    HierarchyStarredStage HMinus j = HierarchyStarredStage H (index j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      hcoreMinus HMinus hcountMinus hstageMinus starredAt j index hz
  obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · subst j
    simpa [hz, HierarchyStarredStage] using hcoreMinus
  · have hi : (index i.succ).val ≠ 0 := by simp [index]
    rw [starredAt (index i.succ) hi]
    exact hstageMinus i.succ

theorem helper_stageSegment_5688.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
    ∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment
      (H.stage
        (⟨a, by
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))))
      (H.stage
        (⟨a + d, by
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      HMinus corrStar baseStar HStar transSegment
  as_aux_lemma =>
    clear * - H transSegment
    intro a d
    induction d with
    | zero => intro hb; exact ⟨le_rfl, by intro i; rfl, by intro i; rfl⟩
    | succ d ih =>
        intro hb
        have hp := ih (by omega)
        have hn := H.nested ⟨a + d, by omega⟩
        exact transSegment hp (by simpa [Nat.add_assoc] using hn)

theorem helper_nextBound_5702.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        (↑j : ℕ) ≠ (0 : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
    TreeSequenceInitialSegment A B →
    (∀ (a d : ℕ) (hb : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage
            (⟨a, by
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))
          (H.stage
            (⟨a + d, by
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ))))) →
    ∀ (i : Fin H.dividerCount),
    (H.stage i.succ.castSucc).length ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H q A
      ell B lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus
      baseMinus HMinus corrStar baseStar HStar starredAt hAB stageSegment i
  as_aux_lemma =>
    have hqpos : 0 < H.dividerCount := by have := i.isLt; omega
    have hqval : 0 < q.val := by simpa [q] using hqpos
    have hA : A = H.stage q.castSucc := starredAt q (by
      intro hz
      exact (Nat.ne_of_gt hqval) hz)
    have hs := stageSegment (i.val + 1) (H.dividerCount - (i.val + 1)) (by
      have := i.isLt
      omega)
    have hlo : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc :=
      Fin.ext rfl
    have hhi : (⟨i.val + 1 + (H.dividerCount - (i.val + 1)), by omega⟩ :
        Fin (H.dividerCount + 2)) = q.castSucc := by
      apply Fin.ext
      simp [q]
    rw [hlo, hhi, ← hA] at hs
    exact le_trans hs.1 hAB.1

theorem helper_edgesMinus_5721.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    B.length + (2 : ℕ) = T.length →
    Bplus.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) R.minus →
    R.minus.length =
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))).length + (1 : ℕ) →
    R.minus.length = B.length + (1 : ℕ) →
    ∀ (r : Fin R.minus.length),
    (∃ (t : Fin T.length),
        (↑t : ℕ) = (↑r : ℕ) ∧ (↑r : ℕ) < B.length ∧ R.minus.edge r = T.edge t) ∨
      (↑r : ℕ) = B.length ∧ R.minus.edge r = T.edge lastIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex ell B
      Bplus lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus
      baseMinus HMinus corrStar baseStar HStar hBL hPL hBT hBM hMinusLen hBMlen r
  as_aux_lemma =>
    by_cases hr : r.val < B.length
    · let i : Fin B.length := ⟨r.val, hr⟩
      have he : Fin.castLE hBM.1 i = r := Fin.ext rfl
      have hprefix : TreeSequenceInitialSegment B R.minus := hBM
      refine Or.inl ⟨Fin.castLE hBT.1 i, rfl, hr, ?_⟩
      rw [← he, hprefix.2.2 i, hBT.2.2 i]
    · have he : r = Fin.cast hBMlen.symm (Fin.last B.length) := by
        apply Fin.ext
        simp
        omega
      exact Or.inr ⟨by have := r.isLt; omega, by rw [he]; exact R.minusFinal.2.2⟩

theorem helper_firstWitness_5737.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar) (X : TreeSequence G e0)
      (c : Fin k),
    (↑(HierarchyFirstMissingPosition phi X c) : ℕ) < X.length →
    c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      HMinus corrStar baseStar HStar X c hc
  let W := Finset.univ.filter fun i : Fin (X.length + 1) =>
    c ∈ MissingColors G phi (X.vertex i)
  by_cases hw : W.Nonempty
  · have he : HierarchyFirstMissingPosition phi X c = W.min' hw := by
      simp only [HierarchyFirstMissingPosition, W, dite_eq_left hw]
    rw [he]
    exact (Finset.mem_filter.mp (Finset.min'_mem W hw)).2
  · have he : HierarchyFirstMissingPosition phi X c = Fin.last X.length := by
      simp only [HierarchyFirstMissingPosition, W, dite_eq_right hw]
    rw [he] at hc
    simp only [Fin.val_last] at hc
    omega

theorem helper_terminalAvoid_5752.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail),
    B.length + (2 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) R.minus →
    R.minus.length =
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))).length + (1 : ℕ) →
    R.minus.length = B.length + (1 : ℕ) →
    R.minus.length + (1 : ℕ) = T.length →
    (∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ))),
        c ∈ MissingColors G phi (X.vertex i) →
          (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ)) →
    (∀ (X : TreeSequence G e0) (c : Fin k) (i : Fin (X.length + (1 : ℕ))),
        (↑i : ℕ) < (↑(HierarchyFirstMissingPosition phi X c) : ℕ) →
          c ∉ MissingColors G phi (X.vertex i)) →
    (∀ (X : TreeSequence G e0) (c : Fin k),
        ∀ t ≤ X.length,
          (∀ (i : Fin (X.length + (1 : ℕ))),
              (↑i : ℕ) < t → c ∉ MissingColors G phi (X.vertex i)) →
            t ≤ (↑(HierarchyFirstMissingPosition phi X c) : ℕ)) →
    (∀ (eta c : Fin k),
        eta ∈ HierarchyStoredColorsAt H q →
          c ∈ C.good.gamma q eta →
            c ∉
              ({c : Fin k |
                  ∃ (r : Fin T.length),
                    A.length ≤ (↑r : ℕ) ∧
                      (↑r : ℕ) <
                          min (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) T.length ∧
                        phi (T.edge r) = some c} :
                Finset (Fin k))) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        theta ∈ C.good.gamma q eta →
          (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤ B.length) →
    (∀ (r : Fin R.minus.length),
        (∃ (t : Fin T.length),
            (↑t : ℕ) = (↑r : ℕ) ∧ (↑r : ℕ) < B.length ∧ R.minus.edge r = T.edge t) ∨
          (↑r : ℕ) = B.length ∧ R.minus.edge r = T.edge lastIndex) →
    (∀ (X : TreeSequence G e0) (c : Fin k),
        (↑(HierarchyFirstMissingPosition phi X c) : ℕ) < X.length →
          c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))) →
    ∀ (eta c : Fin k),
    eta ∈ HierarchyStoredColorsAt H q →
    c ∈ C.good.gamma q eta →
    c ∈
        ({c : Fin k |
            ∃ (r : Fin R.minus.length),
              A.length ≤ (↑r : ℕ) ∧
                (↑r : ℕ) <
                    min (↑(HierarchyFirstMissingPosition phi R.minus eta) : ℕ)
                      R.minus.length ∧
                  phi (R.minus.edge r) = some c} :
          Finset (Fin k)) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H q A
      ell B lastColor lastPosition penPosition endPosition thetaPresent tail R hBL hBT hBM
      hMinusLen hBMlen hminusLen firstLe firstBefore firstLower oldAvoid thetaCutoff edgesMinus
      firstWitness eta c hs hc hm
  as_aux_lemma =>
    obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hm
    have hbeforeU : r.val < (HierarchyFirstMissingPosition phi R.minus eta).val :=
      lt_of_lt_of_le hhi (Nat.min_le_left _ _)
    have hcommonAbsent : ∀ i : Fin (T.length + 1), i.val ≤ B.length →
        i.val ≤ r.val → eta ∉ MissingColors G phi (T.vertex i) := by
      intro i hi hir
      let j : Fin (B.length + 1) := ⟨i.val, by omega⟩
      have hindex : i.val < (HierarchyFirstMissingPosition phi R.minus eta).val := by
        omega
      have hj := firstBefore R.minus eta
        (Fin.castLE (Nat.succ_le_succ hBM.1) j) hindex
      have hvertex : R.minus.vertex (Fin.castLE (Nat.succ_le_succ hBM.1) j) =
          T.vertex i := by
        calc
          _ = B.vertex j := hBM.2.1 j
          _ = T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j) := hBT.2.1 j
          _ = T.vertex i := by congr 1
      rw [hvertex] at hj
      exact hj
    rcases edgesMinus r with ⟨t, htr, htb, hedge⟩ | ⟨hr, hedge⟩
    · have hcut : t.val + 1 ≤ (HierarchyFirstMissingPosition phi T eta).val :=
        firstLower T eta (t.val + 1) (by have := t.isLt; omega) (by
          intro i hi
          exact hcommonAbsent i (by omega) (by omega))
      have hmem : c ∈ Finset.univ.filter (fun c => ∃ r : Fin T.length,
          A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
          phi (T.edge r) = some c) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, t, ?_, ?_, ?_⟩
        · have := t.isLt
          omega
        · have := t.isLt
          omega
        · rw [← hedge]
          exact hcol
      exact oldAvoid eta c hs hc hmem
    · have hcTheta : c = theta := by
        rw [hedge, lastColor] at hcol
        exact (Option.some.inj hcol).symm
      subst c
      have hcut := thetaCutoff eta hs hc
      have hposLT : (HierarchyFirstMissingPosition phi T eta).val < T.length := by
        omega
      have hmissingT := firstWitness T eta hposLT
      let j : Fin (B.length + 1) :=
        ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
      have hjT : Fin.castLE (Nat.succ_le_succ hBT.1) j =
          HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
      have hmissingU : eta ∈ MissingColors G phi
          (R.minus.vertex (Fin.castLE (Nat.succ_le_succ hBM.1) j)) := by
        rw [hBM.2.1 j, ← hBT.2.1 j, hjT]
        exact hmissingT
      have hfirstU := firstLe R.minus eta _ hmissingU
      have hindex := r.isLt
      have : (HierarchyFirstMissingPosition phi R.minus eta).val ≤ B.length := by
        change (HierarchyFirstMissingPosition phi R.minus eta).val ≤ j.val at hfirstU
        have hjval : j.val = (HierarchyFirstMissingPosition phi T eta).val := rfl
        omega
      omega

theorem helper_pathBound_5992.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus),
    HierarchyPathNumber HMinus ≤
      R.minus.length - (HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount)).length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus HMinus
  unfold HierarchyPathNumber
  dsimp only
  split
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ _)).1).2
  · exact le_rfl

theorem helper_hverticesNe_6008.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let alpha : Fin k := D.alpha;
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus),
    HMinus.dividerCount = C.hierarchy.dividerCount →
    ∀ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
    B.length + (2 : ℕ) = T.length →
    Bplus.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    R.minus.length =
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))).length + (1 : ℕ) →
    R.minus.length = B.length + (1 : ℕ) →
    ∀ vAlpha ∈ TreeSequenceVertexSet B,
    alpha ∈ MissingColors G phi vAlpha →
    vAlpha ∈ TreeSequenceVertexSet R.minus →
    vAlpha ≠ T.vertex endIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex
      ell B Bplus lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus
      baseMinus HMinus hcountMinus corrStar baseStar HStar hBL hPL hBT hMinusLen hBMlen vAlpha
      hvAlphaB hmissAlpha hvAlphaMinus he
  obtain ⟨i, hi, rfl⟩ :=
    (@Finset.mem_image _ _ (Classical.decEq V)).mp hvAlphaB
  have heIndex : Fin.castLE (Nat.succ_le_succ hBT.1) i =
      endIndex := by
    apply T.vertex_injective
    exact (hBT.2.1 i).trans he
  have hv := congrArg Fin.val heIndex
  simp only [Fin.val_castLE] at hv
  have hiB : i.val ≤ B.length := Nat.lt_succ_iff.mp i.isLt
  have ht := endPosition
  omega

theorem helper_avoidance_6400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (hcountMinus : HMinus.dividerCount = C.hierarchy.dividerCount)
      (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
      (baseStar : HierarchyBase corrStar.replacementETT phi)
      (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
      (_ : HStar.dividerCount = C.hierarchy.dividerCount)
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HierarchyStarredStage HMinus j =
            HierarchyStarredStage H
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j))
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HierarchyStoredColorsAt HMinus j =
            HierarchyStoredColorsAt H
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j))
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HierarchyStageMissingColors HMinus j =
            HierarchyStageMissingColors H
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j))
      (_ :
        ∀ (eta c : Fin k) (_ : eta ∈ HierarchyStoredColorsAt H q)
          (_ : c ∈ C.good.gamma q eta)
          (_ :
            c ∈
              ({c : Fin k |
                  ∃ (r : Fin R.minus.length),
                    A.length ≤ (↑r : ℕ) ∧
                      (↑r : ℕ) <
                          min (↑(HierarchyFirstMissingPosition phi R.minus eta) : ℕ)
                            R.minus.length ∧
                        phi (R.minus.edge r) = some c} :
                Finset (Fin k))),
          False),
    let index :
      (j : Fin (HMinus.dividerCount + (1 : ℕ))) → Fin (H.dividerCount + (1 : ℕ)) :=
      fun (j : Fin (HMinus.dividerCount + (1 : ℕ))) ↦
      Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j;
    ∀ (_ : index (Fin.last HMinus.dividerCount) = q)
      (_ :
        ∀ (i : Fin HMinus.dividerCount) (eta : Fin k),
          HierarchySegmentColors HMinus i.castSucc eta =
            HierarchySegmentColors H (index i.castSucc) eta)
      (j : Fin (HMinus.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt HMinus j,
    C.good.gamma (index j) eta ⊆
      HierarchyStageMissingColors HMinus j \ HierarchySegmentColors HMinus j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H q A
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      HMinus hcountMinus corrStar baseStar HStar hcountStar starredEq storedEq missingEq
      terminalAvoid index indexLast segmentEq j eta hmem c hc
  have holdMem : eta ∈ HierarchyStoredColorsAt H (index j) := by
    rw [← storedEq j]
    exact hmem
  have hold := Finset.mem_sdiff.mp (C.good.avoidance (index j) eta holdMem hc)
  refine Finset.mem_sdiff.mpr ⟨(missingEq j).symm ▸ hold.1, ?_⟩
  intro hseg
  by_cases hj : j.val < HMinus.dividerCount
  · let i : Fin HMinus.dividerCount := ⟨j.val, hj⟩
    have hij : i.castSucc = j := Fin.ext rfl
    have hOldSeg : c ∈ HierarchySegmentColors H (index j) eta := by
      have hnew : c ∈ HierarchySegmentColors HMinus i.castSucc eta := by
        simpa [hij] using hseg
      have hEq := segmentEq i eta
      have hindex : index j = index i.castSucc := by
        apply Fin.ext
        simp [hij]
      have hmem : c ∈ HierarchySegmentColors H (index i.castSucc) eta := by
        rw [← hEq]
        exact hnew
      simpa [hindex] using hmem
    exact hold.2 hOldSeg
  · have hjlast : j = Fin.last HMinus.dividerCount := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst j
    have havo := terminalAvoid eta c
      (by simpa [index, indexLast] using holdMem)
      (by simpa [index, indexLast] using hc)
      (by
        unfold HierarchySegmentColors at hseg
        dsimp only at hseg
        have hend : HMinus.stage (Fin.last HMinus.dividerCount).succ = R.minus := by
          convert HMinus.terminalStage using 1
          congr 1
        have hlastIndex :
            Fin.cast (congrArg (fun d => d + 1) hcountMinus)
              (Fin.last HMinus.dividerCount) = q := by
          change index (Fin.last HMinus.dividerCount) = q
          exact indexLast
        rw [hend, starredEq (Fin.last HMinus.dividerCount)] at hseg
        simpa [index, indexLast] using hseg)
    exact havo.elim

theorem helper_uniqueRefresh_6451.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (lastColor : phi (T.edge lastIndex) = some theta)
      (lastPosition : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (penPosition : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (endPosition : (↑endIndex : ℕ) = T.length)
      (thetaPresent : theta ∉ MissingColors G phi (T.vertex penIndex)),
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo, pathNumberFull := D.pathNumberFull,
        lastEdgeIndex := lastIndex, penultimateVertexIndex := penIndex,
        terminalVertexIndex := endIndex, lastEdgePosition := lastPosition,
        penultimateVertexPosition := penPosition, terminalVertexPosition := endPosition,
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate, theta := theta,
        thetaOnLastEdge := lastColor, thetaPresentPenultimate := thetaPresent :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx };
    ∀ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx tail)
      (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
      (baseMinus : HierarchyBase corrMinus.replacementETT phi)
      (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
      (hcountMinus : HMinus.dividerCount = C.hierarchy.dividerCount)
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HMinus.stage j.castSucc =
            H.stage
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j).castSucc)
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HierarchyStarredStage HMinus j =
            HierarchyStarredStage H
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j))
      (_ :
        ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
          HierarchyStoredColorsAt HMinus j =
            HierarchyStoredColorsAt H
              (Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j)),
    let index :
      (j : Fin (HMinus.dividerCount + (1 : ℕ))) → Fin (H.dividerCount + (1 : ℕ)) :=
      fun (j : Fin (HMinus.dividerCount + (1 : ℕ))) ↦
      Fin.cast (congrArg (fun (d : ℕ) ↦ d + (1 : ℕ)) hcountMinus) j;
    ∀ (i : Fin HMinus.dividerCount),
    ∃! eta : Fin k,
      eta ∈ HierarchyStoredColorsAt HMinus i.succ ∧
        (C.good.gamma (index i.succ) eta ⊆
            (TreeSequenceVertexSet (HMinus.stage i.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage HMinus i.castSucc)).biUnion
              fun (v : V) ↦ MissingColors G phi v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt HMinus i.succ,
            theta ≠ eta →
              C.good.gamma (index i.succ) theta = C.good.gamma (index i.castSucc) theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D theta lastIndex penIndex endIndex H
      lastColor lastPosition penPosition endPosition thetaPresent tail R corrMinus baseMinus
      HMinus hcountMinus stageEq starredEq storedEq index i
  have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
  let io : Fin H.dividerCount := ⟨i.val, by simpa [hcount] using i.isLt⟩
  have hnext : io.succ = index i.succ := Fin.ext rfl
  have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
  have hnextFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
    Fin.ext rfl
  have hprevFin : Fin.cast (congrArg (fun d =>
      d + 1) hcountMinus) i.castSucc = io.castSucc :=
    Fin.ext rfl
  have hnextIdx : index i.succ = io.succ := by simpa [index] using hnextFin
  have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprevFin
  obtain ⟨chosen, hchosen, hunique⟩ := C.good.uniqueRefresh io
  refine ⟨chosen, ?_, ?_⟩
  · rcases hchosen with ⟨hs, hlocal, hstable⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [storedEq i.succ, hnextFin]
      exact hs
    · rw [stageEq i.succ, starredEq i.castSucc, hnextFin, hprevFin]
      exact hlocal
    · intro theta htheta hne
      have hthetaOld := htheta
      rw [storedEq i.succ] at hthetaOld
      rw [hnextFin] at hthetaOld
      exact hstable theta hthetaOld hne
  · intro eta heta
    have hetaOld : eta ∈ HierarchyStoredColorsAt H io.succ := by
      have hh := heta.1
      rw [storedEq i.succ] at hh
      rw [hnextFin] at hh
      exact hh
    have hlocalOld : C.good.gamma io.succ eta ⊆
        (TreeSequenceVertexSet (H.stage io.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage H io.castSucc)).biUnion
          fun v => MissingColors G phi v := by
      have hh := heta.2.1
      rw [stageEq i.succ, starredEq i.castSucc, hnextFin, hprevFin] at hh
      exact hh
    have hstableOld : ∀ theta ∈ HierarchyStoredColorsAt H io.succ,
        theta ≠ eta → C.good.gamma io.succ theta = C.good.gamma io.castSucc theta := by
      intro theta htheta hne
      have hthetaNew : theta ∈ HierarchyStoredColorsAt HMinus i.succ := by
        have hh : theta ∈ HierarchyStoredColorsAt H (index i.succ) := by
          rw [hnextIdx]
          exact htheta
        rw [storedEq i.succ]
        exact hh
      have hh := heta.2.2 theta hthetaNew hne
      simpa [hnextIdx, hprevIdx] using hh
    apply hunique eta ⟨hetaOld, hlocalOld, hstableOld⟩

theorem helper_continuation_6530.{u_1, u_2} :
    helperContinuation6530Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastColor alphaTerminal alphaBefore lastPosition penPosition
      endPosition thetaPresent tail R corrMinus maxMinus baseMinus hcoreMinus hclosureMinus
      HMinus hcountMinus hstageMinus hpositionMinus corrStar baseStar HStar hcountStar
      transSegment starredAt hBL hPL hBT hAB hBM hMinusLen hBMlen hminusLen vertexMem firstLe
      firstBefore firstLower oldAvoid thetaCutoff terminalData hierarchyInfo stageEq
  have starredEq (j : Fin (HMinus.dividerCount + 1)) :
      HierarchyStarredStage HMinus j = HierarchyStarredStage H
        (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
    (hierarchyInfo j).1
  have storedEq (j : Fin (HMinus.dividerCount + 1)) :
      HierarchyStoredColorsAt HMinus j = HierarchyStoredColorsAt H
        (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
    (hierarchyInfo j).2.1
  have missingEq (j : Fin (HMinus.dividerCount + 1)) :
      HierarchyStageMissingColors HMinus j = HierarchyStageMissingColors H
        (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j) :=
    (hierarchyInfo j).2.2
  have stageSegment : ∀ a d : ℕ,
      ∀ hb : a + d ≤ H.dividerCount + 1,
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
      (H.stage ⟨a + d, by omega⟩) := by
    exact @helper_stageSegment_5688 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@transSegment)
  have nextBound (i : Fin H.dividerCount) :
      (H.stage i.succ.castSucc).length ≤ B.length := by
    exact helper_nextBound_5702 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@starredAt) (@hAB)
        (@stageSegment) (@i)
  have edgesMinus (r : Fin R.minus.length) :
      (∃ t : Fin T.length, t.val = r.val ∧ r.val < B.length ∧
        R.minus.edge r = T.edge t) ∨
      (r.val = B.length ∧ R.minus.edge r = T.edge lastIndex) := by
    exact helper_edgesMinus_5721 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@hBL) (@hPL) (@hBT)
        (@hBM) (@hMinusLen) (@hBMlen) (@r)
  have firstWitness (X : TreeSequence G e0) (c : Fin k)
      (hc : (HierarchyFirstMissingPosition phi X c).val < X.length) :
      c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
    exact helper_firstWitness_5737 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@X) (@c) (@hc)
  have terminalAvoid (eta c : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
      (hc : c ∈ C.good.gamma q eta)
      (hm : c ∈ Finset.univ.filter (fun c => ∃ r : Fin R.minus.length,
        A.length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi R.minus eta).val R.minus.length ∧
        phi (R.minus.edge r) = some c)) : False := by
    exact helper_terminalAvoid_5752 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R) (@hBL)
        (@hBT) (@hBM) (@hMinusLen) (@hBMlen) (@hminusLen) (@firstLe) (@firstBefore) (@firstLower)
        (@oldAvoid) (@thetaCutoff) (@edgesMinus) (@firstWitness) (@eta) (@c) (@hs) (@hc) (@hm)
  let index (j : Fin (HMinus.dividerCount + 1)) : Fin (H.dividerCount + 1) :=
    Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
  have indexZero : index 0 = 0 := Fin.ext rfl
  have indexLast : index (Fin.last HMinus.dividerCount) = q := by
    apply Fin.ext
    simp [index, q]
  have segmentEq (i : Fin HMinus.dividerCount) (eta : Fin k) :
      HierarchySegmentColors HMinus i.castSucc eta =
        HierarchySegmentColors H (index i.castSucc) eta := by
    as_aux_lemma =>
      let io : Fin H.dividerCount := ⟨i.val, by
        have hi := i.isLt
        change HMinus.dividerCount = H.dividerCount at hcountMinus
        omega⟩
      have hnext : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
        Fin.ext rfl
      have hprev : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.castSucc = io.castSucc :=
        Fin.ext rfl
      have hnextIdx : index i.succ = io.succ := by simpa [index] using hnext
      have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprev
      have hcutOld := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta
        (H.stage io.succ.castSucc).length (nextBound io)
      have hcutNew := HierarchyFirstMissingPositionPrefixCutoff phi B R.minus hBM eta
        (H.stage io.succ.castSucc).length (nextBound io)
      have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
      have hio : io.castSucc.succ = io.succ.castSucc := Fin.ext rfl
      unfold HierarchySegmentColors
      dsimp only
      rw [hi, stageEq i.succ, starredEq i.castSucc, hnext, hprev, hprevIdx, hio,
        ← hcutNew, hcutOld]
  let goodMinus : GoodHierarchy HMinus := by
    exact {
      gamma := fun j eta => C.good.gamma (index j) eta
      twoColors := by
        intro j eta hmem
        apply C.good.twoColors (index j) eta
        rw [← storedEq j]
        exact hmem
      avoidance := by
        exact helper_avoidance_6400 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
            (@ctx) (@D)
            (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
            (@corrMinus) (@baseMinus) (@HMinus) (@hcountMinus) (@corrStar) (@baseStar) (@HStar)
            (@hcountStar) (@starredEq) (@storedEq) (@missingEq) (@terminalAvoid) (@indexLast)
            (@segmentEq)
      disjointPairs := by
        intro j eta theta h₁ h₂ hne
        apply C.good.disjointPairs (index j) eta theta
        · rw [← storedEq j]; exact h₁
        · rw [← storedEq j]; exact h₂
        · exact hne
      uniqueRefresh := by
        exact helper_uniqueRefresh_6451 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
            (@ctx) (@D)
            (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
            (@corrMinus) (@baseMinus) (@HMinus) (@hcountMinus) (@stageEq) (@starredEq) (@storedEq)
      parallelBase := by
        dsimp only
        intro hpe
        have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
          terminalData.2.1.symm.trans hpe
        have hold := C.good.parallelBase hpeOld
        rw [hcoreMinus, hclosureMinus, terminalData.1, storedEq 0]
        simpa [indexZero] using hold
      minusClosed := by
        intro i
        have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
        let io : Fin H.dividerCount := ⟨i.val, by simpa [hcount] using i.isLt⟩
        have hnext : io.succ = index i.succ := Fin.ext rfl
        have hprev : io.castSucc = index i.castSucc := Fin.ext rfl
        have hnextFin : Fin.cast (congrArg (fun d => d + 1) hcountMinus) i.succ = io.succ :=
          Fin.ext rfl
        have hprevFin : Fin.cast (congrArg (fun d =>
            d + 1) hcountMinus) i.castSucc = io.castSucc :=
          Fin.ext rfl
        have hprevIdx : index i.castSucc = io.castSucc := by simpa [index] using hprevFin
        have hold := C.good.minusClosed io
        rw [stageEq i.succ, storedEq i.succ]
        rw [hnextFin, hprevIdx]
        exact hold }
  have lastMinus :
      HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) = A := by
    calc
      HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) =
          HierarchyStarredStage H (index (Fin.last HMinus.dividerCount)) :=
        starredEq _
      _ = A := by simpa [A] using congrArg (HierarchyStarredStage H) indexLast
  have pathBound : HierarchyPathNumber HMinus ≤
      R.minus.length - (HierarchyStarredStage HMinus
        (Fin.last HMinus.dividerCount)).length := by
    exact helper_pathBound_5992 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus)
  obtain ⟨vAlpha, hvAlphaB, hmissAlpha⟩ :=
    Finset.mem_biUnion.mp alphaBefore
  have hvAlphaMinus : vAlpha ∈ TreeSequenceVertexSet R.minus :=
    TreeSequenceInitialSegmentVertexSetSubset hBM hvAlphaB
  have hterminalMinus : T.vertex endIndex ∈
      TreeSequenceVertexSet R.minus := by
    rw [← R.minusTerminalVertex]
    exact vertexMem R.minus (Fin.last R.minus.length)
  have hverticesNe : vAlpha ≠ T.vertex endIndex := by
    exact helper_hverticesNe_6008 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@hcountMinus) (@corrStar) (@baseStar) (@HStar)
        (@hBL) (@hPL) (@hBT) (@hMinusLen) (@hBMlen) (@vAlpha) (@hvAlphaB) (@hmissAlpha)
        (@hvAlphaMinus)
  have hnotElementary :
      ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet R.minus) := by
    intro helem
    have hdis := helem hvAlphaMinus hterminalMinus hverticesNe
    exact Finset.disjoint_left.mp hdis hmissAlpha alphaTerminal
  let CMinus : HierarchyCounterexample baseMinus := by
    exact {
      positive := by rw [corrMinus.rungAgreement]; exact C.positive
      hierarchy := HMinus
      good := goodMinus
      maximum := maxMinus
      notElementary := hnotElementary }
  have hpathLess : HierarchyPathNumber HMinus < HierarchyPathNumber H := by
    rw [D.pathNumberFull]
    rw [lastMinus] at pathBound
    change HierarchyPathNumber HMinus < T.length - A.length
    have hlen : R.minus.length + 1 = T.length := by omega
    have hAlen : A.length ≤ R.minus.length := le_trans hAB.1 hBM.1
    omega
  have hmeasureLess : HierarchyCounterexampleLess
      (HierarchyCounterexampleMeasure CMinus)
      (HierarchyCounterexampleMeasure C) := Or.inl hpathLess
  exact (ctx.lexicographicMinimality CMinus corrMinus.rungAgreement hcountMinus)
    hmeasureLess

theorem helper_h_exception_6390.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeOneData G k e0 input T phi ett base C ctx),
    let alpha : Fin k := D.alpha;
    let theta : Fin k := D.theta;
    let lastIndex : Fin T.length := D.lastEdgeIndex;
    let penIndex : Fin (T.length + (1 : ℕ)) := D.penultimateVertexIndex;
    let endIndex : Fin (T.length + (1 : ℕ)) := D.terminalVertexIndex;
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let _ : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : phi (T.edge lastIndex) = some theta)
      (_ : alpha ∈ MissingColors G phi (T.vertex endIndex))
      (_ : alpha ∈ TreeMissingColors phi B)
      (_ : (↑lastIndex : ℕ) + (1 : ℕ) = T.length)
      (_ : (↑penIndex : ℕ) + (1 : ℕ) = T.length)
      (_ : (↑endIndex : ℕ) = T.length)
      (_ : theta ∉ MissingColors G phi (T.vertex penIndex)),
    ∃ eta ∈ HierarchyStoredColorsAt H q,
    eta ∈ MissingColors G phi (T.vertex penIndex) ∧ theta ∈ C.good.gamma q eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D alpha theta lastIndex penIndex endIndex H
      q A ell B Bplus n Tn lastColor alphaTerminal alphaBefore lastPosition penPosition
      endPosition thetaPresent
  as_aux_lemma =>
    let tail : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx :=
      { tailAtLeastTwo := D.tailAtLeastTwo
        pathNumberFull := D.pathNumberFull
        lastEdgeIndex := lastIndex
        penultimateVertexIndex := penIndex
        terminalVertexIndex := endIndex
        lastEdgePosition := lastPosition
        penultimateVertexPosition := penPosition
        terminalVertexPosition := endPosition
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
        theta := theta
        thetaOnLastEdge := lastColor
        thetaPresentPenultimate := thetaPresent }
    obtain ⟨R, hboundaryPE, hrouteMinus, hrouteStar, corrMinus, maxMinus,
        baseMinus, hcoreMinus, hclosureMinus, hsupportMinus, HMinus, hcountMinus,
        hstageMinus, hpositionMinus, corrStar, maxStar, baseStar, hcoreStar,
        hclosureStar, hsupportStar, HStar, hcountStar, hstageStar, hpositionStar⟩ :=
      HierarchySituationTwoReorderedTreesCertified G k e0 input T phi ett base C ctx tail
    by_contra hnone
    have hnone' : ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        eta ∈ MissingColors G phi (T.vertex penIndex) →
        theta ∉ C.good.gamma q eta := by
      intro eta hs hm hgamma
      exact hnone ⟨eta, hs, hm, hgamma⟩
    have transSegment {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      exact helper_transSegment_333 (@G) (@e0) (@hXY) (@hYZ)
    have restrictSegment {X Y Z : TreeSequence G e0}
        (hXZ : TreeSequenceInitialSegment X Z)
        (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
        TreeSequenceInitialSegment X Y := by
      exact helper_restrictSegment_343 (@G) (@e0) (@hXZ) (@hYZ) (@hXY)
    have starredAt (j : Fin (H.dividerCount + 1)) (hj : j.val ≠ 0) :
        HierarchyStarredStage H j = H.stage j.castSucc := by
      as_aux_lemma =>
        obtain hz | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · exact False.elim (hj (congrArg Fin.val hz))
        · rfl
    have hAT : TreeSequenceInitialSegment A T := by
      exact helper_hAT_359 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@starredAt)
    have htail : 2 ≤ ell := D.tailAtLeastTwo
    have hell : ell = T.length - A.length := rfl
    have hBL : B.length + 2 = T.length := by
      simp only [B, HierarchyFullTailPrefix, TreeSequencePrefix]
      change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
      omega
    have hPL : Bplus.length + 1 = T.length := by
      simp only [Bplus, HierarchyFullTailPrefix, TreeSequencePrefix]
      change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
      omega
    have hBT : TreeSequenceInitialSegment B T :=
      ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
    have hBplusT : TreeSequenceInitialSegment Bplus T :=
      ⟨Nat.min_le_right _ _, by intro i; rfl, by intro i; rfl⟩
    have hAB : TreeSequenceInitialSegment A B := restrictSegment hAT hBT (by omega)
    have hBBplus : TreeSequenceInitialSegment B Bplus :=
      restrictSegment hBT hBplusT (by omega)
    have hBM := R.minusFinal.2.1
    have hMinusLen := R.minusFinal.1
    have hBMlen : R.minus.length = B.length + 1 := by omega
    have hBM' : TreeSequenceInitialSegment B R.minus := hBM
    have hBS := transSegment hBM' R.starFinal.2.1
    have hminusLen : R.minus.length + 1 = T.length := by omega
    have hPE : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus) :=
      HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
        ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
        ctx.lexicographicMinimality ctx.largeMissingSet
    have vertexMem (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
        X.vertex i ∈ TreeSequenceVertexSet X := by
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
    have firstLe (X : TreeSequence G e0) (c : Fin k)
        (i : Fin (X.length + 1)) (hi : c ∈ MissingColors G phi (X.vertex i)) :
        (HierarchyFirstMissingPosition phi X c).val ≤ i.val := by
      exact helper_firstLe_400 (@G) (@k) (@e0) (@phi) (@X) (@c) (@i) (@hi)
    have firstMissing (X : TreeSequence G e0) (c : Fin k)
        (hc : c ∈ TreeMissingColors phi X) :
        c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c)) := by
      exact helper_firstMissing_411 (@G) (@k) (@e0) (@phi) (@X) (@c) (@hc)
    have firstBefore (X : TreeSequence G e0) (c : Fin k)
        (i : Fin (X.length + 1))
        (hi : i.val < (HierarchyFirstMissingPosition phi X c).val) :
        c ∉ MissingColors G phi (X.vertex i) := by
      as_aux_lemma =>
        intro hm
        have := firstLe X c i hm
        omega
    have firstLower (X : TreeSequence G e0) (c : Fin k) (t : ℕ)
        (ht : t ≤ X.length)
        (hn : ∀ i : Fin (X.length + 1), i.val < t →
          c ∉ MissingColors G phi (X.vertex i)) :
        t ≤ (HierarchyFirstMissingPosition phi X c).val := by
      exact helper_firstLower_5578 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@D)
          (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
          (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@vertexMem)
          (@firstMissing) (@X) (@c) (@t) (@ht) (@hn)
    have oldAvoid (eta c : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
        (hc : c ∈ C.good.gamma q eta) :
        c ∉ Finset.univ.filter (fun c => ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < min (HierarchyFirstMissingPosition phi T eta).val T.length ∧
          phi (T.edge r) = some c) := by
      exact helper_oldAvoid_453 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@eta) (@c)
          (@hs) (@hc)
    have thetaCutoff (eta : Fin k) (hs : eta ∈ HierarchyStoredColorsAt H q)
        (hc : theta ∈ C.good.gamma q eta) :
        (HierarchyFirstMissingPosition phi T eta).val ≤ B.length := by
      exact helper_thetaCutoff_466 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@D)
          (@lastColor) (@lastPosition) (@penPosition) (@hnone') (@htail) (@hell) (@hBL)
          (@vertexMem) (@firstMissing) (@oldAvoid) (@eta) (@hs) (@hc)
    have terminalData :
        corrMinus.replacementETT.series.data.tree
            (Fin.last corrMinus.replacementETT.rounds).castSucc = Tn ∧
        corrMinus.replacementETT.series.data.kind
            (Fin.last corrMinus.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corrMinus.replacementETT.series.data
            (Fin.last corrMinus.replacementETT.rounds) =
          TashkinovStoredColors ett.series.data n := by
      exact helper_terminalData_5614 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
          (@ctx) (@D)
          (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
          (@corrMinus) (@maxMinus) (@baseMinus) (@hcoreMinus) (@hclosureMinus) (@hsupportMinus)
          (@HMinus) (@hcountMinus) (@hstageMinus) (@hpositionMinus) (@corrStar) (@baseStar) (@HStar)
    have hierarchyInfo : ∀ j : Fin (HMinus.dividerCount + 1),
        let jo := Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
        HierarchyStarredStage HMinus j = HierarchyStarredStage H jo ∧
        HierarchyStoredColorsAt HMinus j = HierarchyStoredColorsAt H jo ∧
        HierarchyStageMissingColors HMinus j = HierarchyStageMissingColors H jo := by
      intro j
      let index := fun j : Fin (HMinus.dividerCount + 1) =>
        Fin.cast (congrArg (fun d => d + 1) hcountMinus) j
      have hz : index 0 = 0 := Fin.ext rfl
      have hstar : HierarchyStarredStage HMinus j = HierarchyStarredStage H (index j) := by
        exact helper_hstar_5654 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
            (@lastColor) (@lastPosition) (@penPosition) (@endPosition) (@thetaPresent) (@R)
            (@corrMinus) (@baseMinus) (@hcoreMinus) (@HMinus) (@hcountMinus) (@hstageMinus)
            (@starredAt) (@j) (@hz)
      refine ⟨hstar, ?_, ?_⟩
      · unfold HierarchyStoredColorsAt
        dsimp only
        rw [terminalData.2.2, hstar]
      · obtain hj | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
        · subst j
          simp [HierarchyStageMissingColors, Tn, n, terminalData.1]
        · have hcount : HMinus.dividerCount = H.dividerCount := hcountMinus
          let io : Fin H.dividerCount := ⟨i.val, by rw [← hcount]; exact i.isLt⟩
          have hi : index i.succ = io.succ := Fin.ext rfl
          simp only [HierarchyStageMissingColors, Fin.cases_succ]
          exact congrArg (TreeMissingColors phi) (hstageMinus i.succ)
    have stageEq (j : Fin (HMinus.dividerCount + 1)) :
        HMinus.stage j.castSucc = H.stage
          (Fin.cast (congrArg (fun d => d + 1) hcountMinus) j).castSucc := hstageMinus j
    exact @helper_continuation_6530 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@lastColor) (@alphaTerminal) (@alphaBefore) (@lastPosition) (@penPosition)
        (@endPosition) (@thetaPresent) (@R) (@corrMinus) (@maxMinus) (@baseMinus) (@hcoreMinus)
        (@hclosureMinus) (@HMinus) (@hcountMinus) (@hstageMinus) (@hpositionMinus) (@corrStar)
        (@baseStar) (@HStar) (@hcountStar) (@transSegment) (@starredAt) (@hBL) (@hPL) (@hBT)
        (@hAB) (@hBM) (@hMinusLen) (@hBMlen) (@hminusLen) (@vertexMem) (@firstLe) (@firstBefore)
        (@firstLower) (@oldAvoid) (@thetaCutoff) (@terminalData) (@hierarchyInfo) (@stageEq)

end GoldbergSeymour.HierarchySituationTwoSubcaseThreeOnePreparation

end
