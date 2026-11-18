/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport

/-!
# Shared stable-change transport along a hierarchy tail

Extracted and generalized from the credited Trellis situation-two proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. The caller supplies its normalized
case premise and original-color agreement; the tail-exclusion continuation is shared.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Agreement on an initial segment and the following edges gives agreement on the whole prefix. -/
theorem TreeSequenceInitialSegment.edgeAgreementOfSplit {V E : Type*}
    {G : LooplessMultigraph V E} {e0 : E} {initial tree : TreeSequence G e0}
    (segment : TreeSequenceInitialSegment initial tree) {k : ℕ}
    {old new : PartialEdgeColoring E k} {bound : ℕ}
    (inside : ∀ index : Fin initial.length, new (initial.edge index) = old (initial.edge index))
    (after : ∀ index : Fin tree.length, initial.length ≤ index.val → index.val < bound →
      new (tree.edge index) = old (tree.edge index))
    (index : Fin tree.length) (before : index.val < bound) :
    new (tree.edge index) = old (tree.edge index) := by
  by_cases inInitial : index.val < initial.length
  · let position : Fin initial.length := ⟨index.val, inInitial⟩
    have same : Fin.castLE segment.1 position = index := Fin.ext rfl
    rw [← same, segment.2.2 position]
    exact inside position
  · exact after index (Nat.le_of_not_gt inInitial) before

/-- Restrict a terminal route to a prefix containing the core and its next edge, then recolor it. -/
theorem ExtendedTashkinovTree.recolorPrefixRoute {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi sigma : PartialEdgeColoring E k}
    {T B : TreeSequence G e0} (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (segment : TreeSequenceInitialSegment B T)
    (penultimate : B.length + 1 = T.length) (coreBound : base.core.length + 1 ≤ B.length)
    (transport : ∀ seed, TashkinovAugmentationSequence phi seed B →
      TashkinovAugmentationSequence sigma seed B) :
    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) B) ∨
    ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
      ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
      ∃ edge seed, ett.series.data.connectingEdges (Fin.last ett.rounds) = {edge} ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) edge seed ∧
        TashkinovAugmentationSequence sigma seed B) := by
  classical
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
    ⟨parallel, route⟩ | ⟨kind, edge, seed, edges, adjoined, _, _, route⟩
  · have inside := TreeSequenceInitialSegment.of_common_extension segment ett.abovePenultimate
      (by have := ett.strictAbovePenultimate; omega)
    exact Or.inl ⟨parallel, transport _
      (TashkinovAugmentationSequenceRestrict phi _ B T route inside segment)⟩
  · have seedInside := TashkinovAugmentationSequenceInitialSegment phi seed T route
    have nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠
        some TashkinovExtensionKind.PE := by
      intro parallel
      rcases kind with kind | kind <;> rw [kind] at parallel <;> cases parallel
    have treeBound : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length ≤
        base.core.length := by rw [base.nonparallel nonparallel]
    have seedBound : seed.length ≤ B.length := by
      have length := adjoined.1
      change seed.length = (ett.series.data.tree (Fin.last ett.rounds).castSucc).length + 1
        at length
      omega
    have inside := TreeSequenceInitialSegment.of_common_extension segment seedInside seedBound
    exact Or.inr ⟨kind, edge, seed, edges, adjoined, transport seed
      (TashkinovAugmentationSequenceRestrict phi seed B T route inside segment)⟩

/-- Dependent contract for transporting a hierarchy through a normalized two-color tail change. -/
abbrev HierarchySituationTwoTailContinuationConditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (theta : Fin k) (penultimate : Fin (T.length + 1)) (root : V ⊕ E),
  theta ∈ MissingColors G phi (T.vertex penultimate) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex penultimate →
  T.vertex penultimate ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex penultimate) →
     c ∉ TreeMissingColors phi A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
        eta) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
       sigma) →
  (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
         old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
  ∀ (beta : Fin k)
   (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) = phi (T.edge t)) →
  let z : V ⊕ E := root;
  beta ≠ theta →
  let ib : Fin (T.length + (1 : ℕ)) :=
   HierarchyFirstMissingPosition phi T beta;
  T.vertex ib ∈ TreeSequenceVertexSet B →
  let rho : PartialEdgeColoring E k := POne.coloring;
  let ettOne :
   ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T
    POne.coloring :=
   POne.corresponding.replacementETT;
  let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
   POne.replacementBase;
  let COne' : HierarchyCounterexample POne.replacementBase :=
   POne.counterexample;
  let _ :
   HierarchyMinimumCounterexampleContext G k e0
    POne.corresponding.replacementInput T POne.coloring
    POne.corresponding.replacementETT POne.replacementBase
    POne.counterexample :=
   POne.minimumContext;
  let HOne :
   TashkinovHierarchy POne.corresponding.replacementETT
    POne.replacementBase :=
   COne'.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
   Fin.last HOne.dividerCount;
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
  theta ∈ MissingColors G rho (T.vertex penultimate) →
  beta ∈ MissingColors G rho (T.vertex ib) →
  HierarchyFirstMissingPosition rho T beta = ib →
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
  (let H := COne'.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ettOne.rounds + 1) := Fin.last ettOne.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ettOne.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ettOne.series.data n
      (0 < H.dividerCount ∧ beta ∈ TreeMissingColors rho Tnq) ∨
        (H.dividerCount = 0 ∧
          (beta ∈ TreeMissingColors rho Tn ∨
            (beta ∈ TreeMissingColors rho A ∧
              beta ∉ Dn ∧ theta ∉ Dn)))) →
  beta ∈ TreeMissingColors rho B ∧ theta ∈ TreeMissingColors rho B →
  Disjoint
    (TwoColorComponent G rho beta theta
     root)
    (TwoColorComponent G rho beta theta (Sum.inl (T.vertex ib))) →
  let muTwo : PartialEdgeColoring E k :=
   TwoColorComponentSwap G rho beta theta z;
  TwoColorPathComponent G rho beta theta z →
  (∀ w ∈ TreeSequenceVertexSet B,
    MissingColors G (TwoColorComponentSwap G rho beta theta z)
      w =
     MissingColors G rho w) →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    HierarchyFirstMissingPosition muTwo T c =
     HierarchyFirstMissingPosition rho T c) →
  TashkinovAugmentationSequence rho B T →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    beta ∈ POne.counterexample.good.gamma qOne c ∨
      theta ∈ POne.counterexample.good.gamma qOne c →
     (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤
      B.length) →
  ∃ (corrTwo :
   CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
   MaximumProperty corrTwo.replacementETT ∧
    ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo)
     (KTwo :
     TashkinovHierarchy corrTwo.replacementETT baseTwo)
     (goodTwo : GoodHierarchy KTwo),
     SameGoodHierarchy COne'.good goodTwo

/-- A stable two-color change preserves the full hierarchy across the fixed tail prefix. -/
theorem HierarchySituationTwoTailContinuation.{u_1, u_2} :
    HierarchySituationTwoTailContinuationConditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx theta penultimate root
      thetaMissingPenultimate H q A B
      htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast
      hcoreLength predecessorIncident seedStable weakEdges beta POne hfixed z hbetaTheta ib hibB
      rho ettOne baseOne' COne' ctxOne HOne qOne hElementaryOne hthetaPenOne hgammaWitnessOne'
      hfirstGammaOne hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo muTwo hpathTwo
      hmissingTwo hstoredTwo hsuffix hgammaCutoff
  have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    z hpathTwo muTwo rfl
    hcaseOne
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
  have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; clear * - htail; omega)
    (by change T.length - A.length - 1 < T.length - A.length; clear * - htail; omega)
    theta (by
      change theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact thetaMissingPenultimate)
  have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht hb
    have hng := hgammaUnusedOne t ht
    by_cases htheta : rho (T.edge t) = some theta
    · let tB : Fin B.length := ⟨t.val, hb⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heOld : phi (T.edge t) = some theta := by
        exact (hfixed t ht).symm.trans htheta
      have heB : phi (B.edge tB) = some theta := by
        rw [← hBT.2.2 tB, hcast]
        exact heOld
      obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
        hthetaExclusion tB ht (by
          change tB.val < A.length + (T.length - A.length - 1)
          have hv := tB.isLt
          clear * - hv htail hBlen
          change tB.val < B.length at hv
          omega) heB
      have hzOne : HOne.dividerCount = 0 := POne.sameGood.1.2.1.symm.trans hz
      have htn : ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc = A :=
        (sameTn POne).trans ((hAzero hz).trans hcore).symm
      have hinc : TreeIncidentEdge
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) (T.edge t) := by
        rw [htn]
        exact predecessorIncident A hAT t hpos
      have hsOld : theta ∈ HierarchyStoredColorsAt H q :=
        Finset.mem_sdiff.mpr ⟨hs, hnotA (c := theta) thetaMissingPenultimate⟩
      have hsOne : theta ∈ HierarchyStoredColorsAt HOne qOne :=
        (sameLast POne).1 ▸ hsOld
      exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzOne).1 _ hinc
        ⟨theta, Finset.mem_union_right _ (Finset.mem_sdiff.mp hsOne).1, htheta⟩
    · simp only [muTwo, TwoColorComponentSwap, hng, htheta, ite_false, ite_self]
  have hfixedCore := weakEdges rho muTwo ettOne baseOne' HOne hstableTwo.1
    ctxOne.oneEdgeUncolored hstableTwo.2.1.2.1
  change ∀ t : Fin (HierarchyStarredStage POne.counterexample.hierarchy
    (Fin.last POne.counterexample.hierarchy.dividerCount)).length,
    muTwo ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) =
    rho ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) at hfixedCore
  rw [sameStar POne] at hfixedCore
  have hfixedPrefix : ∀ t : Fin T.length, t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    exact hAT.edgeAgreementOfSplit hfixedCore hfixedTailTwo
  have transportRoute (S : TreeSequence G e0)
      (hs : TashkinovAugmentationSequence rho S B) :
      TashkinovAugmentationSequence muTwo S B := by
    have fixedEdges (index : Fin B.length) :
        muTwo (B.edge index) = rho (B.edge index) := by
      have fixed := hfixedPrefix (Fin.castLE hBT.1 index) index.isLt
      rwa [hBT.2.2 index] at fixed
    apply TashkinovAugmentationSequence.transport_of_fixed fixedEdges ?_ hs
    intro initial segment _ vertex member
    exact hmissingTwo vertex (TreeSequenceInitialSegmentVertexSetSubset segment member)
  have hrouteTwo :
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
      ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f
              seed ∧
          TashkinovAugmentationSequence muTwo seed B) := by
    apply ettOne.recolorPrefixRoute baseOne' hBT hBlen ?_ transportRoute
    have coreBound : baseOne'.core.length ≤ A.length := by
      rw [← POne.sameGood.1.1]
      exact hcoreLength
    clear * - coreBound htail hBlen
    omega
  exact (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne beta theta hbetaTheta
    (by rw [samePrefix POne]; exact hmissingPairOne)
    z hpathTwo muTwo rfl
    hcaseOne
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
    B (by dsimp only; rw [sameStar POne]; exact hAB)
    (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
    (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
    (by dsimp only; intro t _ ht; exact hfixedPrefix t ht)
    hrouteTwo hsuffix
    ⟨Finset.mem_biUnion.mpr ⟨_, hibB, (hmissingTwo _ hibB).symm ▸ hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩⟩
    (by rw [samePrefix POne]; exact hmissingTwo) hstoredTwo hgammaCutoff).2.2

end GoldbergSeymour

end
