/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SplitSwapData
public import LeanPool.GoldbergSeymour.ElementaryPrefixSwap
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap

/-!
# P2880_T1_Common Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_51.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let _ : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)));
    ∀ (_ : alpha ≠ beta) (e : E) (_ : e ≠ e0),
    ∃ (c : Fin k), TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length))) e = some c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta K hne f hf
  obtain ⟨c, hc⟩ := P.minimumContext.oneEdgeUncolored.2 f hf
  by_cases ha : c = alpha
  · subst c
    by_cases hK : Sum.inr f ∈ K
    · exact ⟨beta, by simp [TwoColorComponentSwap, K, hK, hc]⟩
    · exact ⟨alpha, by simp [TwoColorComponentSwap, K, hK, hc]⟩
  · by_cases hb : c = beta
    · subst c
      by_cases hK : Sum.inr f ∈ K
      · exact ⟨alpha, by simp [TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
      · exact ⟨beta, by simp [TwoColorComponentSwap, K, hK, hc]⟩
    · exact ⟨c, by
        simp [TwoColorComponentSwap, ha, hb, hc]⟩

private theorem helper_hsigmaOne_150.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let _ : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : alpha ≠ beta), IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta K sigma hne
  dsimp [sigma]
  refine ⟨?_, ?_⟩
  · simp [TwoColorComponentSwap, P.minimumContext.oneEdgeUncolored.1]
  · apply helper_branch_51; exact hne
private theorem helper_branch_110.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : H.dividerCount = (0 : ℕ)), TreeSequenceInitialSegment P.replacementBase.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A hz
  have hAeq : A = P.replacementBase.core := by
    obtain hq0 | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · change HierarchyStarredStage H q = P.replacementBase.core
      rw [hq0]
      rfl
    · have hcount : H.dividerCount ≠ 0 := by
        intro h
        have hv := congrArg Fin.val hi
        simp [q, h] at hv
      exact False.elim (hcount hz)
  rw [hAeq]
  exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩

private theorem helper_branch_122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U) (_ :
        TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W)) (_ : (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))))) (_ : ¬H.dividerCount = (0 : ℕ)),
        TreeSequenceInitialSegment P.replacementBase.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A prefixTrans stageSegment hz
  have hstarStage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
    obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · have hcount : H.dividerCount = 0 := by
        have hv := congrArg Fin.val hzero
        simp [q] at hv
        omega
      exact False.elim (hz hcount)
    · change HierarchyStarredStage H q = H.stage ⟨H.dividerCount, by omega⟩
      rw [hi]
      unfold HierarchyStarredStage
      simp only [Fin.cases_succ]
      congr 1
      apply Fin.ext
      simpa [q] using (congrArg Fin.val hi).symm
  rw [hstarStage]
  have hfirst : TreeSequenceInitialSegment P.replacementBase.core
      (H.stage ⟨1, by omega⟩) := H.coreInsideFirst
  have hrest := stageSegment 1 (H.dividerCount - 1) (by omega)
  convert prefixTrans hfirst hrest using 1;
    apply congrArg H.stage; apply Fin.ext; simp; omega

private theorem helper_coreA_303.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U) (_ :
        TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W)) (_ : (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))))), TreeSequenceInitialSegment P.replacementBase.core A
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A prefixTrans stageSegment
  by_cases hz : H.dividerCount = 0
  · apply helper_branch_110; exact hz
  · apply helper_branch_122 <;> assumption
private theorem helper_hlenBX_410.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (_ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (_ : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy)
        (_ : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C),
        let j : ℕ := HierarchyPathNumber C.hierarchy;
        let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
        let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        X.length = B.length + (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hpathLower hpathUpper j B X
  change min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length =
    min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length + 1
  have hj : j < T.length -
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := by
    change j < HierarchyFullTailLength C at hpathUpper
    simpa [HierarchyFullTailLength] using hpathUpper
  have hlow : (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + j ≤ T.length := by omega
  simp [Nat.min_eq_left (by omega :
    (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1) ≤ T.length),
    Nat.min_eq_left (by omega :
    (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 2) ≤ T.length)]
  omega

private theorem helper_branch_303.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (_ : beta ∉ (HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).biUnion (P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount))) (_ : TreeSequenceInitialSegment B X),
    ∀ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∨ beta ∈ P.counterexample.good.gamma q
        eta →
    ∀ eta₀ ∈ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount), alpha ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta₀ → (↑(HierarchyFirstMissingPosition
        P.coloring T eta₀) : ℕ) ≤ (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2
        : ℕ))).length → (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H q j B X D hBetaNotGamma
      hprefixB_X eta hD hgamma eta₀ hD₀ howner hcut
  have hβNotGamma := hBetaNotGamma
  rcases hgamma with hα | hβ
  · have heq : eta = eta₀ := by
      by_contra hneEta
      have hdisjoint := P.counterexample.good.disjointPairs
        q eta eta₀ hD hD₀ hneEta
      exact Finset.disjoint_left.mp hdisjoint hα howner
    subst eta
    exact le_trans hcut hprefixB_X.1
  · exact (hβNotGamma (Finset.mem_biUnion.mpr ⟨eta, hD, hβ⟩)).elim

private theorem helper_hgammaCutoff_610.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (_ : ((alpha ∉ (HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).biUnion (P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount)) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        P.coloring v) ∨
    ∃ eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount), alpha ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition P.coloring
        T eta) : ℕ) ≤ (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2 :
        ℕ))).length)) (_ : beta ∉ (HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).biUnion (P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount))) (_ : TreeSequenceInitialSegment B X),
    ∀ eta ∈ D, alpha ∈ P.counterexample.good.gamma q eta ∨ beta ∈ P.counterexample.good.gamma q
        eta → (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H q j B X D hAlphaChoice
      hBetaNotGamma hprefixB_X eta hD hgamma
  rcases hAlphaChoice with houtside | ⟨eta₀, hD₀, howner, hcut⟩
  · rcases hgamma with hα | hβ
    · exact (houtside (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨eta, hD, hα⟩))).elim
    · exact (hBetaNotGamma
        (Finset.mem_biUnion.mpr ⟨eta, hD, hβ⟩)).elim
  · apply helper_branch_303 <;> assumption
private theorem helper_hseparated_657.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let K : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)));
    ∀ (_ : (
    ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ K)) (_ : TreeSequenceInitialSegment B T) (_ :
        TreeSequenceInitialSegment B X) (_ : X.length = B.length + (1 : ℕ)) (_ : (
    ∀ {rho : PartialEdgeColoring E k} {eta : Fin k} (_ : eta ∈ TreeMissingColors rho B),
        (↑(HierarchyFirstMissingPosition rho T eta) : ℕ) ≤ B.length)) (_ : X.length = A.length +
        (j - (1 : ℕ))),
    ∀ c ∈ TreeMissingColors P.coloring B, Disjoint K (TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T c)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H q j A B X K hsplitAvoid hB_T
      hprefixB_X hlenBX firstPositionBoundOnT hXlen c hc
  let p := HierarchyFirstMissingPosition P.coloring T c
  have hp : p.val ≤ B.length := firstPositionBoundOnT hc
  let ib : Fin (B.length + 1) := ⟨p.val, by omega⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hB_T.1) ib = p := Fin.ext rfl
  have hvB : T.vertex p ∈ TreeSequenceVertexSet B := by
    rw [← hcast, hB_T.2.1 ib]
    simp [TreeSequenceVertexSet]
  have hvX := TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hvB
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hsplitAvoid (T.vertex p) hvX
  change (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk x =
    (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk
      (Sum.inl (T.vertex (Fin.last T.length))) at hx
  change (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk x =
    (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk
      (Sum.inl (T.vertex p)) at hy
  exact hy.symm.trans hx

private theorem helper_hstarToTOriginal_485.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        TreeSequenceInitialSegment
          (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C
  let H₀ := C.hierarchy
  let q₀ : Fin (H₀.dividerCount + 1) := Fin.last H₀.dividerCount
  have starStep : TreeSequenceInitialSegment
      (HierarchyStarredStage H₀ q₀) (H₀.stage q₀.succ) := by
    refine Fin.cases ?_ (fun i => ?_) q₀
    · exact H₀.coreInsideFirst
    · exact H₀.nested i.succ
  have hlast : q₀.succ = Fin.last (H₀.dividerCount + 1) := by
    apply Fin.ext
    rfl
  simpa [H₀, q₀, hlast, H₀.terminalStage] using starStep

private theorem helper_hprefixA_B_507.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : (2 : ℕ) ≤
        HierarchyPathNumber C.hierarchy),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A) (_ :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)) T), TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hpathLower H q j A B hstar hstarToTOriginal
  dsimp only [B, HierarchyFullTailPrefix]
  rw [← hstar]
  have hlen :
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length ≤
        min ((HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length := by
    have hj : 2 ≤ j := by dsimp [j]; exact hpathLower
    exact Nat.le_min.mpr ⟨by omega, hstarToTOriginal.1⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact hstarToTOriginal.2.1 i
  · intro i
    exact hstarToTOriginal.2.2 i

private theorem helper_hB_T_530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    ∀ (_ : (
    ∀ (S : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmS : m ≤ S.length),
        TreeSequenceInitialSegment (TreeSequencePrefix S m hm hmS) S)), TreeSequenceInitialSegment
        B T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C j B prefixOfT
  dsimp [B, HierarchyFullTailPrefix]
  apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
  apply Nat.le_min.mpr
  constructor
  · have hA := (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
    omega
  · exact T.positive

private theorem helper_hX_T_539.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (_ : (
    ∀ (S : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmS : m ≤ S.length),
        TreeSequenceInitialSegment (TreeSequencePrefix S m hm hmS) S)), TreeSequenceInitialSegment
        X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C j X prefixOfT
  dsimp [X, HierarchyFullTailPrefix]
  apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
  apply Nat.le_min.mpr
  constructor
  · have hA := (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
    omega
  · exact T.positive

private theorem helper_hY_T_548.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ : (2 :
        ℕ) ≤ HierarchyPathNumber C.hierarchy),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    ∀ (_ : (
    ∀ (S : TreeSequence G e0) (m : ℕ) (hm : (1 : ℕ) ≤ m) (hmS : m ≤ S.length),
        TreeSequenceInitialSegment (TreeSequencePrefix S m hm hmS) S)), TreeSequenceInitialSegment
        Y T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hpathLower j Y prefixOfT
  dsimp [Y, HierarchyFullTailPrefix]
  apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
  apply Nat.le_min.mpr
  constructor
  · have hA := (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).positive
    omega
  · exact T.positive

private theorem helper_stageSegment_583.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
        [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E)
        (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
          P.counterexample.hierarchy;
        ∀
          (_ :
            (∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U)
              (_ : TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W))
          (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
          TreeSequenceInitialSegment
            (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
            (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H prefixTrans a d
  induction d with
  | zero => intro _; exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  | succ d ih =>
    intro hbound
    have hp := ih (by omega)
    have hn := H.nested ⟨a + d, by omega⟩
    have hn' : TreeSequenceInitialSegment
        (H.stage ⟨a + d, by omega⟩)
        (H.stage ⟨a + (d + 1), by omega⟩) := by
      simpa [Nat.add_assoc] using hn
    exact prefixTrans hp hn'

private theorem helper_hX_Z_634.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : (2 : ℕ) ≤
        HierarchyPathNumber C.hierarchy) (_ : HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S W) (_ :
        TreeSequenceInitialSegment U W) (_ : S.length ≤ U.length), TreeSequenceInitialSegment S
        U)) (_ : TreeSequenceInitialSegment X T),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : TreeSequenceInitialSegment Z T), TreeSequenceInitialSegment X Z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hpathLower hpathUpper j X commonPrefix
      hX_T Z hZ_T
  apply commonPrefix hX_T hZ_T
  change min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length ≤
    min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length +
      (T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length - 1)) T.length
  have hu : j < T.length - (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length := hpathUpper
  exact min_le_min (by omega) le_rfl

private theorem helper_hAXstrict_676.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (_ : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy)
        (_ : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C),
        let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
          P.counterexample.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let j : ℕ := HierarchyPathNumber C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A),
          A.length < X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hpathLower hpathUpper H q j A X hstar
  rw [← hstar]
  change (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length <
    min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length
  have hj : j < T.length -
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := by
    change j < HierarchyFullTailLength C at hpathUpper
    simpa [HierarchyFullTailLength] using hpathUpper
  exact Nat.lt_min.mpr ⟨by omega, by omega⟩

private theorem helper_seedPrefixX_688.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    ∀ (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S W) (_ :
        TreeSequenceInitialSegment U W) (_ : S.length ≤ U.length), TreeSequenceInitialSegment S
        U)) (_ : TreeSequenceInitialSegment A B) (_ : TreeSequenceInitialSegment X T) (_ :
        TreeSequenceInitialSegment B X) (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U) (_ :
        TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W)) (_ :
        TreeSequenceInitialSegment Tn A) (_ : X.length = B.length + (1 : ℕ)) (_ : A.length <
        X.length) {f : E} {seed : TreeSequence G e0} (_ : TreeSequenceAdjoinEdge Tn f seed) (_ :
        TashkinovAugmentationSequence P.coloring seed T), TreeSequenceInitialSegment seed X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q j A B X n Tn commonPrefix hprefixA_B
      hX_T hprefixB_X prefixTrans hTnA hlenBX hAXstrict f seed hadjoin hroute
  have hseedT := TashkinovAugmentationSequenceInitialSegment
    P.coloring seed T hroute
  have hlen : seed.length ≤ X.length := by
    rw [hadjoin.1]
    have hAX := prefixTrans hprefixA_B hprefixB_X
    have hTnA_len := hTnA.1
    have hAXstrict' := hAXstrict
    omega
  exact commonPrefix hseedT hX_T hlen

private theorem helper_routeToX_714.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : TreeSequenceInitialSegment X T) (_ : TreeSequenceInitialSegment Tn X) (_ : (
    have n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    have Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors P.corresponding.replacementETT.series.data
        n; P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence P.coloring Tn T ∨
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        P.corresponding.replacementETT.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TreeIncidentEdge Tn f ∧ (
    ∃ c ∈ TreeMissingColors P.coloring Tn ∪ Dn, P.coloring f = some c) ∧
        TashkinovAugmentationSequence P.coloring seed T)) (_ : (
    ∀ {f : E} {seed : TreeSequence G e0} (_ : TreeSequenceAdjoinEdge Tn f seed) (_ :
        TashkinovAugmentationSequence P.coloring seed T), TreeSequenceInitialSegment seed X)) (_ :
        (
    ∀ {S : TreeSequence G e0} (_ : TashkinovAugmentationSequence P.coloring S X),
        TashkinovAugmentationSequence sigma S X)), P.corresponding.replacementETT.series.data.kind
        n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma Tn X ∨
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        P.corresponding.replacementETT.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j X n Tn sigma hX_T hTnX
      terminalRoute seedPrefixX switchedRoute
  rcases terminalRoute with ⟨hPE, hroute⟩ |
    ⟨hNonPE, f, seed, hconnecting, hadjoin, _, _, hroute⟩
  · exact Or.inl ⟨hPE,
      switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring Tn X T
        hroute hTnX hX_T)⟩
  · rcases hNonPE with hs | hr
    · exact Or.inr ⟨Or.inl hs, f, seed, hconnecting, hadjoin,
        switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring seed X T
          hroute (seedPrefixX hadjoin hroute)
          hX_T)⟩
    · exact Or.inr ⟨Or.inr hr, f, seed, hconnecting, hadjoin,
        switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring seed X T
          hroute (seedPrefixX hadjoin hroute)
          hX_T)⟩

private theorem helper_fixedUntilSplitEnd_822.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : TreeSequenceInitialSegment X T) (_ : (
    ∀ v ∈ TreeSequenceVertexSet X,
    ∀ (f : E), Incident G v f → TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex
        (Fin.last T.length))) f = P.coloring f)) (_ : X.length = B.length + (1 : ℕ)) (r : Fin
        T.length) (_ : (↑r : ℕ) ≤ X.length), sigma (T.edge r) = P.coloring (T.edge r) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j B X sigma hX_T
      hincidentFixed hlenBX r hr
  obtain ⟨i, hi⟩ := T.attaches r
  let ix : Fin (X.length + 1) := ⟨i.val, by omega⟩
  let it : Fin (T.length + 1) :=
    Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ r.isLt))
  have hcast : Fin.castLE (Nat.succ_le_succ hX_T.1) ix = it := Fin.ext rfl
  have hv : T.vertex it = X.vertex ix := by
    rw [← hcast]
    exact hX_T.2.1 ix
  apply hincidentFixed (T.vertex it)
    (by rw [hv]; simp [TreeSequenceVertexSet]) (T.edge r)
  change T.vertex it ∈ G.ends (T.edge r)
  rw [hi]
  exact Sym2.mem_mk_right _ _

private theorem helper_hXlen_837.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (_ : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy)
        (_ : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C),
        let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
          P.counterexample.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let j : ℕ := HierarchyPathNumber C.hierarchy;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
        ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A),
          X.length = A.length + (j - (1 : ℕ)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hpathLower hpathUpper H q j A X hstar
  rw [← hstar]
  change min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length =
    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
      (j - 1)
  have hu : j < T.length - (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length := hpathUpper
  omega

private theorem helper_htailP_1034.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
          P.counterexample.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A),
          HierarchyFullTailLength P.counterexample = HierarchyFullTailLength C := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A hstar
  change T.length - A.length =
    T.length - (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length
  rw [← hstar]

private theorem helper_hprefixP_1039.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
        (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
        (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
        (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
        (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
          P.counterexample.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A)
          (i : ℕ), HierarchyFullTailPrefix P.counterexample i = HierarchyFullTailPrefix C i := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A hstar i
  have hs : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
      HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) := hstar
  unfold HierarchyFullTailPrefix
  dsimp only
  simp only [← hs]

private theorem helper_hZeq_1049.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ :
        HierarchyFullTailLength P.counterexample = HierarchyFullTailLength C) (_ : (
    ∀ (i : ℕ), HierarchyFullTailPrefix P.counterexample i = HierarchyFullTailPrefix C i)),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
        HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ)) = Z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P htailP hprefixP Z
  rw [htailP, hprefixP]

private theorem helper_hZElementary_1056.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1
        : ℕ)) = Z), ColoredVertexSetElementary G P.coloring (TreeSequenceVertexSet Z) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P Z hZeq
  rw [← hZeq]
  exact HierarchyCounterexamplePenultimateElementary G k e0
    P.corresponding.replacementInput T P.coloring
    P.corresponding.replacementETT P.replacementBase P.counterexample
    P.minimumContext.proper P.minimumContext.oneEdgeUncolored
    P.minimumContext.lowerRung P.minimumContext.fewerDividers
    P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet

private theorem helper_hB_missingEq_1068.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let K : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : alpha ≠ beta) (_ : (
    ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ K)) (_ : TreeSequenceInitialSegment B X),
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G P.coloring v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j B X K sigma hne hsplitAvoid
      hprefixB_X v hv
  have hvX : v ∈ TreeSequenceVertexSet X :=
    TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv
  have hbehavior := TwoColorComponentSwapMissingBehavior G P.coloring
    alpha beta hne P.minimumContext.proper
    (Sum.inl (T.vertex (Fin.last T.length)))
  exact hbehavior.1 v (hsplitAvoid v hvX)

private theorem helper_hfixedX_1077.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : (
    ∀ v ∈ TreeSequenceVertexSet X,
    ∀ (f : E), Incident G v f → TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex
        (Fin.last T.length))) f = P.coloring f)) (t : Fin X.length), sigma (X.edge t) = P.coloring
        (X.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j X sigma hincidentFixed t
  obtain ⟨i, hi⟩ := X.attaches t
  apply hincidentFixed (X.vertex t.succ) (by simp [TreeSequenceVertexSet])
    (X.edge t)
  change X.vertex t.succ ∈ G.ends (X.edge t)
  rw [hi]
  exact Sym2.mem_mk_left _ _

private theorem helper_switchedRoute_1094.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : TreeSequenceInitialSegment B X) (_ : (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G P.coloring v)) (_ : (
    ∀ (t : Fin X.length), sigma (X.edge t) = P.coloring (X.edge t))) (_ : X.length = B.length + (1
        : ℕ)) {S : TreeSequence G e0} (_ : TashkinovAugmentationSequence P.coloring S X),
        TashkinovAugmentationSequence sigma S X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j B X sigma hprefixB_X
      hB_missingEq hfixedX hlenBX S hroute
  exact TashkinovAugmentationSequenceColoringTransport
    P.coloring sigma S B X hroute hprefixB_X hlenBX
      (by intro t _; exact hfixedX t) hB_missingEq

private theorem helper_oldSuffix_1100.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    ∀ (_ : TreeSequenceInitialSegment X T) (_ : TreeSequenceInitialSegment Tn X) (_ : (
    have n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    have Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors P.corresponding.replacementETT.series.data
        n; P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence P.coloring Tn T ∨
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        P.corresponding.replacementETT.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TreeIncidentEdge Tn f ∧ (
    ∃ c ∈ TreeMissingColors P.coloring Tn ∪ Dn, P.coloring f = some c) ∧
        TashkinovAugmentationSequence P.coloring seed T)) (_ : (
    ∀ {f : E} {seed : TreeSequence G e0} (_ : TreeSequenceAdjoinEdge Tn f seed) (_ :
        TashkinovAugmentationSequence P.coloring seed T), TreeSequenceInitialSegment seed X)),
        TashkinovAugmentationSequence P.coloring X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P j X n Tn hX_T hTnX terminalRoute seedPrefixX
  rcases terminalRoute with ⟨_, hroute⟩ |
    ⟨_, f, seed, _, hadjoin, _, _, hroute⟩
  · exact TashkinovAugmentationSequenceSuffix P.coloring Tn X T hroute
      hTnX hX_T
  · exact TashkinovAugmentationSequenceSuffix P.coloring seed X T hroute
      (seedPrefixX hadjoin hroute) hX_T

private theorem helper_oldMissingOnZ_1182.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    ∀ (_ : TreeSequenceInitialSegment B X),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : TreeSequenceInitialSegment X Z) {c : Fin k} (_ : c ∈ TreeMissingColors P.coloring B), c
        ∈ TreeMissingColors P.coloring Z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P j B X hprefixB_X Z hX_Z c hc
  obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
  exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hX_Z
    (TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv), hm⟩

private theorem helper_branch_1216.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1
        : ℕ)) = Z) (_ : TreeSequenceInitialSegment X Z), TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 : ℕ)))
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1 :
        ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P j X Z hZeq hX_Z
  rw [hZeq]
  exact hX_Z

private theorem helper_branch_1218.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1
        : ℕ)) = Z) (_ : ColoredVertexSetElementary G P.coloring (TreeSequenceVertexSet Z)),
        ColoredVertexSetElementary G P.coloring (TreeSequenceVertexSet (HierarchyFullTailPrefix
        P.counterexample (HierarchyFullTailLength P.counterexample - (1 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P Z hZeq hZElementary
  rw [hZeq]
  exact hZElementary

private theorem helper_branch_1220.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : TreeSequenceInitialSegment X Z) (_ : (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) v = MissingColors G P.coloring v)) (_ : (
    ∀ (t : Fin X.length), sigma (X.edge t) = P.coloring (X.edge t))), TreeColoringInvariant
        (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 : ℕ))) P.coloring
        (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length))))
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta j X sigma Z hX_Z hpenMissing
      hfixedX
  refine ⟨fun r _ => hfixedX r, ?_⟩
  intro v hv
  exact hpenMissing v (TreeSequenceInitialSegmentVertexSetSubset hX_Z hv)

private theorem helper_branch_1223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (_ : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : (
    ∀ (r : Fin T.length) (_ : (↑r : ℕ) ≤ X.length), sigma (T.edge r) = P.coloring (T.edge r))) (_
        : X.length = A.length + (j - (1 : ℕ))),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    ∀ (r : Fin T.length) (_ : A.length ≤ (↑r : ℕ)) (_ : (↑r : ℕ) < A.length + j),
        TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
        (T.edge r) = P.coloring (T.edge r) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hpathLower H q j A X sigma
      fixedUntilSplitEnd hXlen
  dsimp only
  intro r _ hr
  apply fixedUntilSplitEnd r
  rw [hXlen]
  change r.val < A.length + j at hr
  have hj : 2 ≤ j := hpathLower
  omega

private theorem helper_branch_1232.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (_ : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) (_ : alpha ≠
        beta), beta ∈ MissingColors G (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)))) (T.vertex (Fin.last T.length)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hAlphaTerminal hne
  exact (TwoColorComponentSwapMissingBehavior G P.coloring alpha beta hne
    P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.1
      (T.vertex (Fin.last T.length)) rfl hAlphaTerminal

private theorem helper_branch_1235.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1
        : ℕ)) = Z) (_ : (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) v = MissingColors G P.coloring v)),
    ∀ v ∈ TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength
        P.counterexample - (1 : ℕ))), MissingColors G (TwoColorComponentSwap G P.coloring alpha
        beta (Sum.inl (T.vertex (Fin.last T.length)))) v = MissingColors G P.coloring v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta Z hZeq hpenMissing
  rw [hZeq]
  exact hpenMissing

private abbrev helperContinuation2539Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let j : ℕ := HierarchyPathNumber C.hierarchy;
    ∀ (_ : (2 : ℕ) ≤ j) (_ : j < HierarchyFullTailLength C),
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let K : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)));
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length)));
    ∀ (_ : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) (_ : alpha ∈
        TreeMissingColors P.coloring B) (_ : (alpha ∉ (HierarchyStoredColorsAt
        P.counterexample.hierarchy q).biUnion (P.counterexample.good.gamma q) ∪
        (TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn).biUnion fun (v :
        V) ↦ MissingColors G P.coloring v) ∨
    ∃ eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy q, alpha ∈
        P.counterexample.good.gamma q eta ∧ (↑(HierarchyFirstMissingPosition P.coloring T eta) :
        ℕ) ≤ B.length) (_ : beta ∈ TreeMissingColors P.coloring B) (_ : beta ∉
        (HierarchyStoredColorsAt P.counterexample.hierarchy q).biUnion
        (P.counterexample.good.gamma q)) (_ : alpha ≠ beta) (_ : TwoColorPathComponent G
        P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) (_ : sigma = sigma) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (_ :
    ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ K) (_ : HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A) (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B T) (_ : TreeSequenceInitialSegment X T) (_ :
        TreeSequenceInitialSegment B X) (_ :
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) (_ : TreeSequenceInitialSegment P.replacementBase.core
        A),
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ∀ (_ : HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - (1
        : ℕ)) = Z) (_ : TreeSequenceInitialSegment X Z) (_ : ColoredVertexSetElementary G
        P.coloring (TreeSequenceVertexSet Z)) (_ :
    ∀ v ∈ TreeSequenceVertexSet X,
    ∀ (f : E), Incident G v f → TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex
        (Fin.last T.length))) f = P.coloring f) (_ :
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G (TwoColorComponentSwap G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) v = MissingColors G P.coloring v) (_ :
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G P.coloring v) (_ :
    ∀ (t : Fin X.length), sigma (X.edge t) = P.coloring (X.edge t)) (_ : X.length = B.length + (1
        : ℕ)) (_ : A.length < X.length) (_ : TashkinovAugmentationSequence P.coloring X T) (_ :
        P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X ∨
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0),
        P.corresponding.replacementETT.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) (_ : alpha
        ∈ TreeMissingColors sigma X ∧ beta ∈ TreeMissingColors sigma X) (_ :
        TashkinovAugmentationSequence sigma X T) (_ :
    ∀ {rho : PartialEdgeColoring E k} {eta : Fin k} (_ : eta ∈ TreeMissingColors rho B),
        (↑(HierarchyFirstMissingPosition rho T eta) : ℕ) ≤ B.length) (_ :
    ∀ (eta : Fin k) (_ : eta ∈ TreeMissingColors P.coloring B), HierarchyFirstMissingPosition
        sigma T eta = HierarchyFirstMissingPosition P.coloring T eta), Nonempty
        (P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P alpha beta sigma)

private theorem helper_continuation_2539.{u_1, u_2} :
    helperContinuation2539Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H q j hpathLower hpathUpper A
      B X n Tn D K sigma hAlphaTerminal hAlphaB hAlphaChoice hBetaB hBetaNotGamma hne hpath
      hsigma hsigmaProper hsigmaOne hsplitAvoid hstar hprefixA_B hB_T hX_T hprefixB_X prefixTrans
      coreA Z hZeq hX_Z hZElementary hincidentFixed hpenMissing hB_missingEq hfixedX hlenBX
      hAXstrict oldSuffix routeToX hsplitMissing switchedSuffix firstPositionBoundOnT
      firstPositionEqualOnTail
  with_reducible_and_instances
    have firstPositionGloballyEqual (eta : Fin k) (first : eta ≠ alpha) (second : eta ≠ beta) :
        HierarchyFirstMissingPosition
            (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length))))
            T eta = HierarchyFirstMissingPosition P.coloring T eta := by
      apply TreeSequenceFirstMissingPositionMembershipCongr
      intro index
      exact (TwoColorComponentSwapMissingBehavior G P.coloring alpha beta hne
        P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.2.2
          (T.vertex index) eta first second
    have hstoredFirst : ∀ eta ∈ D, HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition P.coloring T eta := by
      intro eta _
      by_cases isAlpha : eta = alpha
      · subst eta
        exact firstPositionEqualOnTail alpha hAlphaB
      · by_cases isBeta : eta = beta
        · subst eta
          exact firstPositionEqualOnTail beta hBetaB
        · exact firstPositionGloballyEqual eta isAlpha isBeta
    have hgammaCutoff := @helper_hgammaCutoff_610 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@hAlphaChoice) (@hBetaNotGamma) (@hprefixB_X)
    have hAX : TreeSequenceInitialSegment A X :=
      prefixTrans hprefixA_B hprefixB_X
    have fixedUntilSplitEnd := @helper_fixedUntilSplitEnd_822 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@hX_T) (@hincidentFixed) (@hlenBX)
    have hXlen := @helper_hXlen_837 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hpathLower) (@hpathUpper) (@hstar)
    have hseparated := @helper_hseparated_657 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
        (@beta) (@hsplitAvoid) (@hB_T) (@hprefixB_X) (@hlenBX) (@firstPositionBoundOnT) (@hXlen)
    have missingOnB {color : Fin k} (member : color ∈ TreeMissingColors P.coloring B) :
        color ∈ TreeMissingColors sigma B := by
      rwa [TreeMissingColors.congr hB_missingEq]
    have oldMissingOnZ := @helper_oldMissingOnZ_1182 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@hprefixB_X) (@hX_Z)
    refine ⟨{
      swapped := hsigma
      distinct := hne
      path := hpath
      splitOutside := hsplitAvoid
      twoBeforeInSplit := hprefixB_X
      splitInFull := hX_T
      splitAboveStar := ⟨hAX, hAXstrict⟩
      splitInPenultimate := ?_
      coreInSplit := prefixTrans coreA hAX
      penultimateElementary := ?_
      proper := hsigmaProper
      oneEdgeUncolored := hsigmaOne
      invariant := ?_
      incidentFixed := hincidentFixed
      fixedOnSplit := fun r hr => fixedUntilSplitEnd r (Nat.le_of_lt hr)
      fixedThroughJ := ?_
      missingTwoBefore := ⟨missingOnB hAlphaB, missingOnB hBetaB⟩
      missingOnSplit := hsplitMissing
      oldMissingOnPenultimate := ?_
      missingTerminal := ?_
      penultimateMissing := ?_
      storedFirst := hstoredFirst
      gammaCutoff := hgammaCutoff
      separatedAlpha := hseparated alpha hAlphaB
      separatedBeta := hseparated beta hBetaB
      prefixRoute := routeToX
      oldSuffix := oldSuffix
      newSuffix := switchedSuffix }⟩
    · exact @helper_branch_1216 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hZeq) (@hX_Z)
    · exact @helper_branch_1218 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hZeq) (@hZElementary)
    · exact @helper_branch_1220 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@hX_Z) (@hpenMissing) (@hfixedX)
    · exact @helper_branch_1223 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@hpathLower) (@fixedUntilSplitEnd) (@hXlen)
    · rw [hZeq]
      exact ⟨oldMissingOnZ hAlphaB, oldMissingOnZ hBetaB⟩
    · exact @helper_branch_1232 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@hAlphaTerminal) (@hne)
    · exact @helper_branch_1235 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@hZeq) (@hpenMissing)

private theorem helper_continuation_1137.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (_ : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy) (_ : HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C) (_ : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last
        T.length))) (_ : alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C
        (HierarchyPathNumber C.hierarchy - (2 : ℕ)))) (_ : ((alpha ∉ (HierarchyStoredColorsAt
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
        (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)) ∪
        (TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet
        (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G
        P.coloring v) ∨
    ∃ eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount), alpha ∈ P.counterexample.good.gamma (Fin.last
        P.counterexample.hierarchy.dividerCount) eta ∧ (↑(HierarchyFirstMissingPosition P.coloring
        T eta) : ℕ) ≤ (HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2 :
        ℕ))).length)) (_ : beta ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C
        (HierarchyPathNumber C.hierarchy - (2 : ℕ)))) (_ : beta ∉ (HierarchyStoredColorsAt
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
        (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount))) (_ :
        alpha ≠ beta) (_ : TwoColorPathComponent G P.coloring alpha beta (Sum.inl (T.vertex
        (Fin.last T.length)))) (_ : (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length))) : PartialEdgeColoring E k) = TwoColorComponentSwap G
        P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) (_ : IsProperEdgeColoring
        G (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))
        : PartialEdgeColoring E k)) (_ : IsOneEdgeUncolored (TwoColorComponentSwap G P.coloring
        alpha beta (Sum.inl (T.vertex (Fin.last T.length))) : PartialEdgeColoring E k) e0) (_ : (
    ∀ v ∈ TreeSequenceVertexSet (HierarchyFullTailPrefix C ((HierarchyPathNumber C.hierarchy : ℕ)
        - (1 : ℕ)) : TreeSequence G e0), Sum.inl v ∉ (TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length))) : Set (V ⊕ E)))) (_ : HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) = (HierarchyStarredStage
        (P.counterexample.hierarchy : TashkinovHierarchy P.corresponding.replacementETT
        P.replacementBase) (Fin.last (P.counterexample.hierarchy : TashkinovHierarchy
        P.corresponding.replacementETT P.replacementBase).dividerCount : Fin
        ((P.counterexample.hierarchy : TashkinovHierarchy P.corresponding.replacementETT
        P.replacementBase).dividerCount + (1 : ℕ))) : TreeSequence G e0)) (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S W) (_ :
        TreeSequenceInitialSegment U W) (_ : S.length ≤ U.length), TreeSequenceInitialSegment S
        U)) (_ : TreeSequenceInitialSegment (HierarchyStarredStage (P.counterexample.hierarchy :
        TashkinovHierarchy P.corresponding.replacementETT P.replacementBase) (Fin.last
        (P.counterexample.hierarchy : TashkinovHierarchy P.corresponding.replacementETT
        P.replacementBase).dividerCount : Fin ((P.counterexample.hierarchy : TashkinovHierarchy
        P.corresponding.replacementETT P.replacementBase).dividerCount + (1 : ℕ))) : TreeSequence
        G e0) (HierarchyFullTailPrefix C ((HierarchyPathNumber C.hierarchy : ℕ) - (2 : ℕ)) :
        TreeSequence G e0)) (_ : TreeSequenceInitialSegment (HierarchyFullTailPrefix C
        ((HierarchyPathNumber C.hierarchy : ℕ) - (2 : ℕ)) : TreeSequence G e0) T) (_ :
        TreeSequenceInitialSegment (HierarchyFullTailPrefix C ((HierarchyPathNumber C.hierarchy :
        ℕ) - (1 : ℕ)) : TreeSequence G e0) T) (_ : TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C ((HierarchyPathNumber C.hierarchy : ℕ) - (2 : ℕ)) :
        TreeSequence G e0) (HierarchyFullTailPrefix C ((HierarchyPathNumber C.hierarchy : ℕ) - (1
        : ℕ)) : TreeSequence G e0)) (_ : (
    ∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U) (_ :
        TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W)) (_ :
        TreeSequenceInitialSegment P.replacementBase.core (HierarchyStarredStage
        (P.counterexample.hierarchy : TashkinovHierarchy P.corresponding.replacementETT
        P.replacementBase) (Fin.last (P.counterexample.hierarchy : TashkinovHierarchy
        P.corresponding.replacementETT P.replacementBase).dividerCount : Fin
        ((P.counterexample.hierarchy : TashkinovHierarchy P.corresponding.replacementETT
        P.replacementBase).dividerCount + (1 : ℕ))) : TreeSequence G e0)) (_ :
        TreeSequenceInitialSegment (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds : Fin (P.corresponding.replacementETT.rounds + (1 :
        ℕ))).castSucc : TreeSequence G e0) P.replacementBase.core), Nonempty
        (P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P alpha beta
        (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))))
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta hpathLower hpathUpper
  set H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      P.counterexample.hierarchy
  set q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount
  set j : ℕ := HierarchyPathNumber C.hierarchy
  set A : TreeSequence G e0 := HierarchyStarredStage H q
  set B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ))
  set X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ))
  set n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
      P.corresponding.replacementETT.rounds
  set Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc
  let D : Finset (Fin k) :=
    HierarchyStoredColorsAt H q
  set K : Set (V ⊕ E) := TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
      T.length)))
  set sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
      (T.vertex (Fin.last T.length)))
  intro hAlphaTerminal hAlphaB hAlphaChoice hBetaB hBetaNotGamma hne hpath hsigma hsigmaProper
      hsigmaOne hsplitAvoid hstar commonPrefix hprefixA_B hB_T hX_T hprefixB_X prefixTrans coreA
      hTnCore
  -- Keep the hierarchy computations folded while assembling their established properties.
  with_reducible_and_instances
    have hTnA : TreeSequenceInitialSegment Tn A := prefixTrans hTnCore coreA
    have hTnX : TreeSequenceInitialSegment Tn X :=
      prefixTrans hTnA (prefixTrans hprefixA_B hprefixB_X)
    have terminalRoute := P2813_T1_TerminalRoute G k e0
      P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT
    have htailP := @helper_htailP_1034 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hstar)
    have hprefixP := @helper_hprefixP_1039 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hstar)
    let Z := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
    have hZeq := @helper_hZeq_1049 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@htailP) (@hprefixP)
    have hZ_T : TreeSequenceInitialSegment Z T := by
      unfold TreeSequenceInitialSegment Z HierarchyFullTailPrefix TreeSequencePrefix
      exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have hX_Z := @helper_hX_Z_634 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hpathLower)
        (@hpathUpper) (@commonPrefix) (@hX_T) (@hZ_T)
    have hZElementary := @helper_hZElementary_1056 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@hZeq)
    obtain ⟨hincidentFixed, hpenMissing⟩ := P2880_T1_ElementaryPrefixSwap G P.coloring
      alpha beta hne P.minimumContext.proper B X Z hprefixB_X hX_Z hZElementary
      hAlphaB hBetaB (Sum.inl (T.vertex (Fin.last T.length))) hsplitAvoid
    have hB_missingEq := @helper_hB_missingEq_1068 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@hne) (@hsplitAvoid) (@hprefixB_X)
    have hfixedX := @helper_hfixedX_1077 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
        (@beta) (@hincidentFixed)
    have hlenBX := @helper_hlenBX_410 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hpathLower) (@hpathUpper)
    have hAXstrict := @helper_hAXstrict_676 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hpathLower) (@hpathUpper) (@hstar)
    have seedPrefixX := @helper_seedPrefixX_688 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@commonPrefix) (@hprefixA_B) (@hX_T) (@hprefixB_X) (@prefixTrans) (@hTnA) (@hlenBX)
        (@hAXstrict)
    have switchedRoute := @helper_switchedRoute_1094 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P) (@alpha) (@beta) (@hprefixB_X) (@hB_missingEq) (@hfixedX) (@hlenBX)
    have oldSuffix := @helper_oldSuffix_1100 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hX_T)
        (@hTnX) (@terminalRoute) (@seedPrefixX)
    have routeToX := @helper_routeToX_714 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
        (@beta) (@hX_T) (@hTnX) (@terminalRoute) (@seedPrefixX) (@switchedRoute)
    have hAlphaMissingX : alpha ∈ TreeMissingColors sigma X := by
      apply TreeSequenceInitialSegment.treeMissingColors_subset hprefixB_X
      rwa [TreeMissingColors.congr hB_missingEq]
    have hBetaMissingX : beta ∈ TreeMissingColors sigma X := by
      apply TreeSequenceInitialSegment.treeMissingColors_subset hprefixB_X
      rwa [TreeMissingColors.congr hB_missingEq]
    have hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧
        beta ∈ TreeMissingColors sigma X := ⟨hAlphaMissingX, hBetaMissingX⟩
    have switchedSuffix : TashkinovAugmentationSequence sigma X T :=
      TashkinovAugmentationSequenceComponentSwap G k e0 P.coloring alpha beta
        hne (Sum.inl (T.vertex (Fin.last T.length))) X T oldSuffix
        hsplitMissing.1 hsplitMissing.2
    have firstPositionBoundOnT {rho : PartialEdgeColoring E k} {eta : Fin k}
        (missing : eta ∈ TreeMissingColors rho B) :
        (HierarchyFirstMissingPosition rho T eta).val ≤ B.length :=
      TreeSequenceFirstMissingPositionLePrefix hB_T missing
    have firstPositionEqualOnTail (eta : Fin k) (missing : eta ∈ TreeMissingColors P.coloring B) :
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition P.coloring T eta :=
      TreeSequenceFirstMissingPositionCongrOfPrefix hB_T hB_missingEq missing
    exact @helper_continuation_2539 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@beta) (@hpathLower) (@hpathUpper) (@hAlphaTerminal) (@hAlphaB) (@hAlphaChoice)
        (@hBetaB) (@hBetaNotGamma) (@hne) (@hpath) (@hsigma) (@hsigmaProper) (@hsigmaOne)
        (@hsplitAvoid) (@hstar) (@hprefixA_B) (@hB_T) (@hX_T) (@hprefixB_X) (@prefixTrans)
        (@coreA) (@hZeq) (@hX_Z) (@hZElementary) (@hincidentFixed) (@hpenMissing) (@hB_missingEq)
        (@hfixedX) (@hlenBX) (@hAXstrict) (@oldSuffix) (@routeToX) (@hsplitMissing)
        (@switchedSuffix) (@firstPositionBoundOnT) (@firstPositionEqualOnTail)
theorem P2880_T1_CommonPreparation
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) ∧
        alpha ∈ TreeMissingColors P.coloring B ∧
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          ∃ eta : Fin k, eta ∈ D ∧
            alpha ∈ P.counterexample.good.gamma q eta ∧
            (HierarchyFirstMissingPosition P.coloring T eta).val ≤
              B.length))
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          ∃ r : Fin T.length,
            A.length ≤ r.val ∧ r.val < A.length + j ∧
              P.coloring (T.edge r) = some c
      beta ≠ alpha ∧
        beta ∈ TreeMissingColors P.coloring B ∧
        beta ∉ Gamma ∧ beta ∉ tailUsedThroughJ ∧
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D ∧
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ))
    (hcomponentDisjoint :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      let Q := TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))
      ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ Q) :
    Nonempty (P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta (TwoColorComponentSwap G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length))))) := by
  classical
  let H := P.counterexample.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let j := HierarchyPathNumber C.hierarchy
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (j - 2)
  let X := HierarchyFullTailPrefix C (j - 1)
  let Y := HierarchyFullTailPrefix C j
  let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
    Fin.last P.corresponding.replacementETT.rounds
  let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (P.counterexample.good.gamma q)
  let K := TwoColorComponent G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  let sigma := TwoColorComponentSwap G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  rcases halpha with ⟨hAlphaTerminal, hAlphaB, hAlphaChoice⟩
  rcases hbeta with ⟨hBetaNe, hBetaB, hBetaNotGamma, hBetaNotUsed, hBetaChoice⟩
  have hne : alpha ≠ beta := by
    intro he
    exact hBetaNe he.symm
  have hpath : TwoColorPathComponent G P.coloring alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) :=
    TwoColorPathComponent.of_missing P.minimumContext.proper hne hAlphaTerminal
  have hsigma : sigma = TwoColorComponentSwap G P.coloring alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) := rfl
  have hsigmaProper : IsProperEdgeColoring G sigma := by
    dsimp [sigma]
    exact TwoColorComponentSwapProper G P.coloring alpha beta hne
      P.minimumContext.proper _
  have hsigmaOne := @helper_hsigmaOne_150 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hne)
  have hsplitAvoid : ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ K := by
    simpa only [X, K] using hcomponentDisjoint
  have hstar : HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount) = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy P.counterexample.hierarchy P.sameGood.1).1
  have hstarToTOriginal := @helper_hstarToTOriginal_485 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
  have hA_T : TreeSequenceInitialSegment A T := by
    rw [← hstar]
    exact hstarToTOriginal
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
      (bound : S.length ≤ U.length) : TreeSequenceInitialSegment S U :=
    hUW.of_common_extension hSW bound
  have hprefixA_B := @helper_hprefixA_B_507 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
      (@hpathLower) (@hstar) (@hstarToTOriginal)
  have prefixOfT (S : TreeSequence G e0) (m : ℕ)
      (hm : 1 ≤ m) (hmS : m ≤ S.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix S m hm hmS) S := by
    refine ⟨hmS, ?_, ?_⟩
    · intro i
      simp [TreeSequencePrefix]
    · intro i
      simp [TreeSequencePrefix]
  have hB_T := @helper_hB_T_530 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@prefixOfT)
  have hX_T := @helper_hX_T_539 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@prefixOfT)
  have hY_T := @helper_hY_T_548 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hpathLower) (@prefixOfT)
  have hprefixB_X : TreeSequenceInitialSegment B X := by
    apply commonPrefix hB_T hX_T
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length ≤
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length
    have hj : 2 ≤ j := by dsimp [j]; exact hpathLower
    exact min_le_min (by omega) le_rfl
  have hprefixX_Y : TreeSequenceInitialSegment X Y := by
    apply commonPrefix hX_T hY_T
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length ≤
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + j) T.length
    exact min_le_min (by omega) le_rfl
  have prefixTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := hSU.trans hUW
  have stageSegment := @helper_stageSegment_583 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
      (@prefixTrans)
  have coreA := @helper_coreA_303 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@prefixTrans)
      (@stageSegment)
  have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
    by_cases hpe : P.corresponding.replacementETT.series.data.kind n =
        some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := P.replacementBase.parallel hpe
      simpa [Tn, n] using u.leftSegment
    · rw [P.replacementBase.nonparallel hpe]
      exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  exact @helper_continuation_1137 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@hpathLower) (@hpathUpper) (@hAlphaTerminal) (@hAlphaB) (@hAlphaChoice) (@hBetaB)
      (@hBetaNotGamma) (@hne) (@hpath) (@hsigma) (@hsigmaProper) (@hsigmaOne) (@hsplitAvoid)
      (@hstar) (@commonPrefix) (@hprefixA_B) (@hB_T) (@hX_T) (@hprefixB_X) (@prefixTrans)
      (@coreA) (@hTnCore)
end GoldbergSeymour

end
