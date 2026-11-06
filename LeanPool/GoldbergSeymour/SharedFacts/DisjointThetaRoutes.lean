/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.TerminalRoute

/-!
# Disjoint-theta replacement routes

The stored and unstored branches use these same replacement and route transport proofs.
Extracted from Wesley Pegden's pinned Trellis formalization during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.DisjointThetaRoutes

/-- Shared transport fact for the two disjoint-theta proof branches. -/
theorem terminalRouteToPrefix.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
        (j : ℕ), HierarchyPathNumber C.hierarchy = j → (2 : ℕ) ≤ j →
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
        TreeSequenceInitialSegment A T → (
    ∀ {U W : TreeSequence G e0}, TreeSequenceInitialSegment U T → TreeSequenceInitialSegment W T →
        U.length ≤ W.length → TreeSequenceInitialSegment U W) → Y.length = A.length + j →
        TreeSequenceInitialSegment Y T → TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment A Y → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k) (et :
        ExtendedTashkinovTree G k e0 input' T old) (bs : HierarchyBase et old) (K :
        TashkinovHierarchy et bs), HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
        IsOneEdgeUncolored old e0 → IsOneEdgeUncolored new e0 →
    ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length), new
        ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) = old ((HierarchyStarredStage
        K (Fin.last K.dividerCount)).edge t)) → Y.length = X.length + (1 : ℕ) →
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (nu :
        PartialEdgeColoring E k), IsOneEdgeUncolored nu e0 → HierarchyWeaklyStable
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) nu → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → nu (T.edge t) = S.coloring
        (T.edge t)) → (
    ∀ v ∈ TreeSequenceVertexSet Z, MissingColors G nu v = MissingColors G S.coloring v) →
    let et : ExtendedTashkinovTree G k e0 S.corresponding.replacementInput T S.coloring :=
        S.corresponding.replacementETT;
    let n : Fin (et.rounds + (1 : ℕ)) := Fin.last et.rounds;
    let Tn : TreeSequence G e0 := et.series.data.tree n.castSucc; et.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence nu Tn Y ∨ (et.series.data.kind n
        = some TashkinovExtensionKind.SE ∨ et.series.data.kind n = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (seed : TreeSequence G e0), et.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence nu seed Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j hj hpathLower R H q A ell
      X Y Z hAtoT commonPrefix hYlen hYtoT hXtoY hYtoZ hAtoY sameStarAll weakEdges hXYlen S nu hn
      hw hf hm
  as_aux_lemma =>
    have hj : 2 ≤ j := hpathLower
    clear * - G k e0 input T phi ett base C ctx S nu hn hw hf hm
      A X Y Z hAtoT hYtoT hXtoY hYtoZ hXYlen hAtoY hYlen hj j sameStarAll
      commonPrefix weakEdges
    clear_value A X Y Z
    let et := S.corresponding.replacementETT
    let K := S.counterexample.hierarchy
    let Tn := et.series.data.tree (Fin.last et.rounds).castSucc
    have hTnT : TreeSequenceInitialSegment Tn T := et.abovePenultimate
    have hTnA : Tn.length ≤ A.length := by
      by_cases hz : K.dividerCount = 0
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
        have hs := sameStarAll S
        change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
        rw [hi] at hs
        change S.replacementBase.core = A at hs
        by_cases hp : et.series.data.kind (Fin.last et.rounds) =
            some TashkinovExtensionKind.PE
        · rw [← hs]; exact (Classical.choice (S.replacementBase.parallel hp).2.2).leftSegment.1
        · rw [← hs, S.replacementBase.nonparallel hp]
      · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
            (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
          Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
        have hs := sameStarAll S
        change HierarchyStarredStage K (Fin.last K.dividerCount) = A at hs
        rw [hi] at hs
        have hmono : Monotone (fun i : Fin (K.dividerCount + 2) => (K.stage i).length) :=
          Fin.monotone_iff_le_succ.mpr (fun i => (K.nested i).1)
        rw [← hs]
        change Tn.length ≤ (K.stage _).length
        rw [show Tn = K.stage 0 from K.baseStage.symm]
        exact hmono (Fin.zero_le _)
    have hAYstrict : A.length < Y.length := by
      clear * - hj hYlen
      omega
    have fixedA : ∀ t : Fin A.length, nu (A.edge t) = S.coloring (A.edge t) := by
      have he := weakEdges S.coloring nu et S.replacementBase K hw
        S.minimumContext.oneEdgeUncolored hn
      change ∀ t : Fin (HierarchyStarredStage S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount)).length,
          nu ((HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) =
          S.coloring ((HierarchyStarredStage S.counterexample.hierarchy
            (Fin.last S.counterexample.hierarchy.dividerCount)).edge t) at he
      rw [sameStarAll S] at he
      exact he
    have fixedY : ∀ t : Fin Y.length, nu (Y.edge t) = S.coloring (Y.edge t) := by
      intro t
      let tT : Fin T.length := Fin.castLE hYtoT.1 t
      have he : T.edge tT = Y.edge t := hYtoT.2.2 t
      by_cases ht : t.val < A.length
      · let tA : Fin A.length := ⟨t.val, ht⟩
        have hcast : Fin.castLE hAtoT.1 tA = tT := Fin.ext rfl
        rw [← he, ← hcast, hAtoT.2.2 tA]
        exact fixedA tA
      · rw [← he]
        exact hf tT (Nat.le_of_not_gt ht) t.isLt
    have transport (W : TreeSequence G e0)
        (hr : TashkinovAugmentationSequence S.coloring W Y) :
        TashkinovAugmentationSequence nu W Y :=
      TashkinovAugmentationSequenceColoringTransport S.coloring nu W X Y hr
        hXtoY hXYlen (fun t _ => fixedY t)
        (fun v hv => hm v (TreeSequenceInitialSegmentVertexSetSubset hYtoZ
          (TreeSequenceInitialSegmentVertexSetSubset hXtoY hv)))
    rcases P2813_T1_TerminalRoute G k e0 S.corresponding.replacementInput T
      S.coloring et with ⟨hp, hr⟩ | ⟨hk, f, seed, he, ha, _, _, hr⟩
    · have hTY : TreeSequenceInitialSegment Tn Y :=
        commonPrefix hTnT hYtoT (hTnA.trans hAtoY.1)
      exact Or.inl ⟨hp, transport Tn
        (TashkinovAugmentationSequenceRestrict S.coloring Tn Y T hr hTY hYtoT)⟩
    · have hseedT : TreeSequenceInitialSegment seed T :=
        TashkinovAugmentationSequenceInitialSegment S.coloring seed T hr
      have hseedY : TreeSequenceInitialSegment seed Y :=
        commonPrefix hseedT hYtoT (by
          have hl := ha.1
          change seed.length = Tn.length + 1 at hl
          clear * - hl hTnA hAYstrict
          omega)
      exact Or.inr ⟨hk, f, seed, he, ha, transport seed
        (TashkinovAugmentationSequenceRestrict S.coloring seed Y T hr hseedY hYtoT)⟩

/-- Shared transport fact for the two disjoint-theta proof branches. -/
theorem changeReplacementColoring.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta)
        (j : ℕ),
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let Y : TreeSequence G e0 := HierarchyFullTailPrefix C j;
    let Z : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (gamma : Fin k), (↑(HierarchyFirstMissingPosition sigma T d.theta) : ℕ) = Y.length → gamma ≠
        d.theta → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage S.counterexample.hierarchy (Fin.last
        S.counterexample.hierarchy.dividerCount) = A) → (
    ∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix S.counterexample (HierarchyFullTailLength S.counterexample - (1 :
        ℕ)) = Z) →
    ∀ (R1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := R1.coloring; ColoredVertexSetElementary G rho
        (TreeSequenceVertexSet Z) → HierarchyFirstMissingPosition rho T gamma =
        HierarchyFirstMissingPosition sigma T gamma → HierarchyFirstMissingPosition rho T d.theta
        = HierarchyFirstMissingPosition sigma T d.theta → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < Y.length → rho (T.edge t) ≠ some gamma)
        → (↑(HierarchyFirstMissingPosition sigma T gamma) : ℕ) < (↑(HierarchyFirstMissingPosition
        sigma T d.theta) : ℕ) → gamma ∈ TreeMissingColors rho Z ∧ d.theta ∈ TreeMissingColors rho
        Z →
    let H : TashkinovHierarchy R1.corresponding.replacementETT R1.replacementBase :=
        R1.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R1.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R1.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R1.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R1.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition rho T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition rho T d.theta);
    have sameComponent : Prop := TwoColorComponent G rho gamma d.theta (Sum.inl va) =
        TwoColorComponent G rho gamma d.theta (Sum.inl vb); ( (0 : ℕ) < H.dividerCount ∧ (gamma ∈
        TreeMissingColors rho Tnq ∨ Disjoint { gamma, d.theta } Dnq) → sameComponent) ∧ (
        H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors rho Tn ∨ Disjoint { gamma, d.theta }
        Dn) → sameComponent) ∧ ( gamma ∈ TreeMissingColors rho A ∧ TreeColorSetClosed G rho A
        { gamma } → sameComponent ∧ TreeInterchangeable G A rho gamma d.theta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d j R sigma H q A ell Y Z
      gamma hthetaFirstIndex hgammaNeTheta sameStarAll samePenultimate R1 rho hElemRho
      hfirstGammaRho hfirstThetaRho hgammaUnusedRho hgammaBeforeTheta hpairMissingRho
  as_aux_lemma =>
    exact ChangeLemma G k e0 R1.corresponding.replacementInput T rho
      R1.corresponding.replacementETT R1.replacementBase R1.counterexample
      R1.minimumContext.proper R1.minimumContext.oneEdgeUncolored R1.minimumContext.lowerRung
      R1.minimumContext.fewerDividers R1.minimumContext.lexicographicMinimality
      (by change ColoredVertexSetElementary G rho
            (TreeSequenceVertexSet (HierarchyFullTailPrefix R1.counterexample
              (HierarchyFullTailLength R1.counterexample - 1)))
          rw [samePenultimate R1]; exact hElemRho)
      R1.minimumContext.largeMissingSet gamma d.theta hgammaNeTheta
      (by change gamma ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength R1.counterexample
                - 1)) ∧
            d.theta ∈ TreeMissingColors rho
              (HierarchyFullTailPrefix R1.counterexample (HierarchyFullTailLength
                  R1.counterexample - 1))
          rw [samePenultimate R1]; exact hpairMissingRho)
      (by
        dsimp only
        rw [sameStarAll R1, hfirstGammaRho, hfirstThetaRho]
        intro _
        refine ⟨⟨_, _, rfl, rfl, hgammaBeforeTheta⟩, ?_⟩
        intro hc
        obtain ⟨_, t, hlo, hhi, he⟩ := Finset.mem_filter.mp hc
        rw [hthetaFirstIndex] at hhi
        exact hgammaUnusedRho t hlo hhi he)

/-- Shared transport fact for the two disjoint-theta proof branches. -/
theorem firstReplacementChange.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (d : HierarchySituationThreeDisjointData G k e0 input T phi ett base C ctx P alpha beta),
    let R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := d.switched;
    let sigma : PartialEdgeColoring E k := R.coloring;
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (gamma : Fin k), gamma ≠ beta → HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = A → ( gamma ∉ TreeMissingColors sigma A ∨ beta ∉
        TreeMissingColors sigma A → TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition
        sigma T gamma)) (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧ gamma ∉ ({c :
        Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑(HierarchyFirstMissingPosition sigma
        T beta) : ℕ) ∧ sigma (T.edge t) = some c} : Finset (Fin k))) → ColoredVertexSetElementary
        G sigma (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ)))) → gamma ∈ TreeMissingColors sigma
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ))) ∧ beta ∈ TreeMissingColors sigma (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - (1 : ℕ))) →
    let H : TashkinovHierarchy R.corresponding.replacementETT R.replacementBase :=
        R.counterexample.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (R.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        R.corresponding.replacementETT.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := R.corresponding.replacementETT.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors R.corresponding.replacementETT.series.data
        n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition sigma T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition sigma T beta);
    have sameComponent : Prop := TwoColorComponent G sigma gamma beta (Sum.inl va) =
        TwoColorComponent G sigma gamma beta (Sum.inl vb); ( (0 : ℕ) < H.dividerCount ∧ (gamma ∈
        TreeMissingColors sigma Tnq ∨ Disjoint (insert gamma ({ beta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ ( H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        sigma Tn ∨ Disjoint (insert gamma ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ ( gamma ∈ TreeMissingColors sigma A ∧ TreeColorSetClosed G sigma A
        ({ gamma } : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A sigma gamma beta)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta d R sigma H q A gamma
      hgammaNeBeta sameStar horderedUnusedGammaBeta hchangeElementary hchangeMissing
  as_aux_lemma =>
    exact ChangeLemma G k e0 R.corresponding.replacementInput T sigma
      R.corresponding.replacementETT R.replacementBase R.counterexample
      R.minimumContext.proper R.minimumContext.oneEdgeUncolored
      R.minimumContext.lowerRung R.minimumContext.fewerDividers
      R.minimumContext.lexicographicMinimality hchangeElementary
      R.minimumContext.largeMissingSet gamma beta hgammaNeBeta hchangeMissing
      (by
        change (gamma ∉ TreeMissingColors sigma A ∨ beta ∉ TreeMissingColors sigma A) →
          TreeVertexOrder T
              (T.vertex (HierarchyFirstMissingPosition sigma T gamma))
              (T.vertex (HierarchyFirstMissingPosition sigma T beta)) ∧
            gamma ∉ (Finset.univ.filter fun c =>
              ∃ t : Fin T.length, A.length ≤ t.val ∧
                t.val < (HierarchyFirstMissingPosition sigma T beta).val ∧
                  sigma (T.edge t) = some c)
        exact horderedUnusedGammaBeta)

end GoldbergSeymour.SharedFacts.DisjointThetaRoutes

end
