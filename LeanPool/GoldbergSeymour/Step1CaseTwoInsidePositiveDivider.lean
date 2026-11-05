/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryColorVertex
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeVertexOrder
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Case Two Inside Positive Divider

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_355.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), (0 : ℕ) < ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good : GoodHierarchy H),
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).card →
    ∀ (alpha beta : Fin k) (a₁ b₁ a₂ b₂ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl a₁) (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl
        a₂) (Sum.inl b₂)), (
    ∀ x ∈ P₁.support, x ∉ P₂.support) → a₁ ≠ a₂ →
    ∀ (theta : Fin k), theta ≠ beta → (
    ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0) (corr :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma T'), IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 → StableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
        sigma → MaximumProperty corr.replacementETT →
    ∀ (base' : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT base') (good' : GoodHierarchy K), K.dividerCount < H.dividerCount → (2
        : ℕ) * corr.replacementETT.rounds + (11 : ℕ) ≤ (TreeMissingColors sigma
        (corr.replacementETT.series.data.tree (Fin.last
        corr.replacementETT.rounds).castSucc)).card → TreeColorSetMinusClosed G sigma T'
        ((HierarchyTerminalStoredColors K).biUnion (good'.gamma (Fin.last K.dividerCount))) →
    ∀ (a b : Fin k), a ≠ b → a ∈ TreeMissingColors sigma T' → TreeColorSetClosed G sigma T' ({ a }
        : Finset (Fin k)) →
    ∀ (u₁ v₁ u₂ v₂ : V) (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₁) (Sum.inl v₁))
        (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₂) (Sum.inl v₂)), TreeExitPath
        T' sigma a b u₁ v₁ Q₁ → TreeExitPath T' sigma a b u₂ v₂ Q₂ → (
    ∀ x ∈ Q₁.support, x ∉ Q₂.support) → u₁ ≠ u₂ → False) → (0 : ℕ) < H.dividerCount →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount); A = H.stage
        (Fin.last H.dividerCount).castSucc →
    let nu : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha theta;
        IsProperEdgeColoring G nu → IsOneEdgeUncolored nu e0 →
    ∀ (Q₁ : (TwoColorIncidenceGraph G nu theta beta).Walk (Sum.inl a₁) (Sum.inl b₁)), TreeExitPath
        A nu theta beta a₁ b₁ Q₁ → Q₁.support = P₁.support →
    ∀ (Q₂ : (TwoColorIncidenceGraph G nu theta beta).Walk (Sum.inl a₂) (Sum.inl b₂)), TreeExitPath
        A nu theta beta a₂ b₂ Q₂ → Q₂.support = P₂.support → TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆ TreeSequenceVertexSet T →
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi nu → (
    ∀ {B : TreeSequence G e0}, TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet T →
        TreeMissingColors nu B = TreeMissingColors phi B) → theta ∈ TreeMissingColors nu A →
        TreeColorSetClosed G nu A ({ theta } : Finset (Fin k)) →
    ∀ (corrNu : CorrespondingExtendedTashkinovTree G k e0 ett nu T), MaximumProperty
        corrNu.replacementETT →
    ∀ (baseNu : HierarchyBase corrNu.replacementETT nu) (HNu : TashkinovHierarchy
        corrNu.replacementETT baseNu) (goodNu : GoodHierarchy HNu), SameGoodHierarchy good goodNu
        → H.dividerCount = HNu.dividerCount → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H good hlarge alpha beta a₁ b₁ a₂ b₂ P₁
      P₂ hpaths₁₂ ha₁₂ theta hthetaBeta hnoSmaller hdividerPositive A hAstage nu hnuProper hnuOne
      Q₁ hQ₁ hsQ₁ Q₂ hQ₂ hsQ₂ ladderSub hstableLadder treeMissingFixed hthetaNu hthetaClosedNu
      corrNu hMPNu baseNu HNu goodNu hsame hcount
  have hstage : HEq H.stage HNu.stage := hsame.1.2.2.1
  have sameStage (i : Fin (H.dividerCount + 2)) :
      H.stage i = HNu.stage (Fin.cast (congrArg (fun d => d + 2) hcount) i) := by
    have stageEq {d d' : ℕ} (hc : d = d')
        (f : Fin (d + 2) → TreeSequence G e0)
        (g : Fin (d' + 2) → TreeSequence G e0) (he : HEq f g)
        (j : Fin (d + 2)) : f j = g (Fin.cast (congrArg (fun d => d + 2) hc) j) := by
      cases hc
      cases he
      rfl
    exact stageEq hcount H.stage HNu.stage hstage i
  let r : Fin (HNu.dividerCount + 1) := Fin.last HNu.dividerCount
  have hr : 1 ≤ r.val := by simp [r]; omega
  have hANu : A = HNu.stage r.castSucc := by
    rw [hAstage, sameStage]
    apply congrArg HNu.stage
    apply Fin.ext
    simp [r]
  obtain ⟨ettPrefix, hMPPrefix, hroundPrefix, hseriesPrefix, basePrefix,
      hcorePrefix, hclosurePrefix, hsupportPrefix, K, hcountPrefix, hstagesPrefix,
      hdividersPrefix, goodPrefix, hcolorsPrefix, hminusPrefix⟩ :=
    GoodHierarchyPrefixRepackage G k e0 corrNu.replacementInput T nu nu
      corrNu.replacementETT hMPNu baseNu HNu goodNu r hr
  let corrPrefix : CorrespondingExtendedTashkinovTree G k e0 ett nu
      (HNu.stage r.castSucc) :=
    { replacementInput := corrNu.replacementInput
      replacementSeries := corrNu.replacementSeries
      replacementETT := ettPrefix
      rungAgreement := hroundPrefix.trans corrNu.rungAgreement
      seriesPresentation := hseriesPrefix.trans corrNu.seriesPresentation
      finalGeneratingColoring := corrNu.finalGeneratingColoring
      ladderTreesAgree := corrNu.ladderTreesAgree
      storedColorsAgree := corrNu.storedColorsAgree
      connectingEdgesAgree := corrNu.connectingEdgesAgree
      extensionKindsAgree := corrNu.extensionKindsAgree
      replacementProper := corrNu.replacementProper
      replacementOneUncolored := corrNu.replacementOneUncolored
      replacementStable := corrNu.replacementStable }
  have seriesTree {m n : ℕ} {p : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 p) (s' : TashkinovSeries G k n e0 p)
      (he : m = n) (hs : HEq s s') (i : Fin (m + 2)) :
      s.data.tree i = s'.data.tree (Fin.cast (congrArg (fun d => d + 2) he) i) := by
    cases he
    cases hs
    rfl
  have lastTree {B : TreeSequence G e0}
      (c : CorrespondingExtendedTashkinovTree G k e0 ett nu B) :
      c.replacementETT.series.data.tree (Fin.last c.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rw [seriesTree c.replacementETT.series c.replacementSeries c.rungAgreement
      c.seriesPresentation]
    convert c.ladderTreesAgree ⟨ett.rounds - 1, by omega⟩ using 1
    · congr 1
      apply Fin.ext
      simp
      have he := c.rungAgreement
      omega
    · congr 1
      apply Fin.ext
      simp
      omega
  have hlargePrefix : 2 * corrPrefix.replacementETT.rounds + 11 ≤
      (TreeMissingColors nu (corrPrefix.replacementETT.series.data.tree
        (Fin.last corrPrefix.replacementETT.rounds).castSucc)).card := by
    have hm : TreeMissingColors nu
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) :=
      treeMissingFixed ladderSub
    rw [lastTree corrPrefix, hm, corrPrefix.rungAgreement]
    exact hlarge
  have lastStored {m n : ℕ} {p : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 p) (s' : TashkinovSeries G k n e0 p)
      (he : m = n) (hs : HEq s s') :
      TashkinovStoredColors s.data (Fin.last m) =
        TashkinovStoredColors s'.data (Fin.last n) := by
    cases he
    cases hs
    rfl
  have hstoredPrefix : HierarchyTerminalStoredColors K = HierarchyStoredColorsAt HNu r := by
    have hstar : HierarchyStarredStage HNu r = HNu.stage r.castSucc := by
      let i : Fin HNu.dividerCount := ⟨HNu.dividerCount - 1, by omega⟩
      have hi : i.succ = r := by apply Fin.ext; simp [i, r]; omega
      rw [← hi]
      simp [HierarchyStarredStage]
    change TashkinovStoredColors ettPrefix.series.data (Fin.last ettPrefix.rounds) \
        TreeMissingColors nu (HNu.stage r.castSucc) =
      TashkinovStoredColors corrNu.replacementETT.series.data
          (Fin.last corrNu.replacementETT.rounds) \
        TreeMissingColors nu (HierarchyStarredStage HNu r)
    rw [lastStored ettPrefix.series corrNu.replacementETT.series hroundPrefix hseriesPrefix,
      hstar]
  have hgammaPrefix : goodPrefix.gamma (Fin.last K.dividerCount) =
      goodNu.gamma ⟨r.val - 1, by omega⟩ := by
    let j : Fin r.val := ⟨r.val - 1, by omega⟩
    have hc := (hcolorsPrefix j).2
    have hi : (Fin.cast (by omega) j :
        Fin (K.dividerCount + 1)) = Fin.last K.dividerCount := by
      apply Fin.ext
      exact hcountPrefix.symm
    funext eta
    simpa [hi, j] using hc eta
  have hterminalPrefix : TreeColorSetMinusClosed G nu (HNu.stage r.castSucc)
      ((HierarchyTerminalStoredColors K).biUnion
        (goodPrefix.gamma (Fin.last K.dividerCount))) := by
    rw [hstoredPrefix, hgammaPrefix]
    exact hminusPrefix
  have hsmall : K.dividerCount < H.dividerCount := by
    have hc := hcountPrefix
    simp [r] at hc
    omega
  have hmissingPrefix : theta ∈ TreeMissingColors nu (HNu.stage r.castSucc) := by
    rw [← hANu]
    exact hthetaNu
  have hclosedPrefix : TreeColorSetClosed G nu (HNu.stage r.castSucc) {theta} := by
    rw [← hANu]
    exact hthetaClosedNu
  have hQ₁Prefix : TreeExitPath (HNu.stage r.castSucc) nu theta beta a₁ b₁ Q₁ := by
    rw [← hANu]
    exact hQ₁
  have hQ₂Prefix : TreeExitPath (HNu.stage r.castSucc) nu theta beta a₂ b₂ Q₂ := by
    rw [← hANu]
    exact hQ₂
  exact hnoSmaller nu (HNu.stage r.castSucc) corrPrefix hnuProper hnuOne
    hstableLadder hMPPrefix basePrefix K goodPrefix hsmall hlargePrefix
    hterminalPrefix theta beta hthetaBeta hmissingPrefix hclosedPrefix
    a₁ b₁ a₂ b₂ Q₁ Q₂ hQ₁Prefix hQ₂Prefix
    (by simpa [hsQ₁, hsQ₂] using hpaths₁₂) ha₁₂

private theorem helper_continuation_361.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), MaximumProperty ett → (0 : ℕ) < ett.rounds → IsProperEdgeColoring G phi →
        IsOneEdgeUncolored phi e0 → LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H) (_ :
        ℕ), (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)).card →
    ∀ (alpha beta : Fin k), alpha ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
        TreeExitPath T phi alpha beta a₁ b₁ P₁ → TreeExitPath T phi alpha beta a₂ b₂ P₂ →
        TreeExitPath T phi alpha beta a₃ b₃ P₃ → (
    ∀ x ∈ P₁.support, x ∉ P₂.support) → a₁ ≠ a₂ →
    ∀ (f₃ : E), Sum.inr f₃ ∈ P₃.support → b₃ ∈ TreeSequenceVertexSet (HierarchyStarredStage H
        (Fin.last H.dividerCount)) →
    ∀ (theta : Fin k), theta ≠ beta → theta ∈ TreeMissingColors phi (HierarchyStarredStage H
        (Fin.last H.dividerCount)) → TreeColorSetClosed G phi (HierarchyStarredStage H (Fin.last
        H.dividerCount)) ({ theta } : Finset (Fin k)) → (
    ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0) (corr :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma T'), IsProperEdgeColoring G sigma →
        IsOneEdgeUncolored sigma e0 → StableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
        sigma → MaximumProperty corr.replacementETT →
    ∀ (base' : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT base') (good' : GoodHierarchy K), K.dividerCount < H.dividerCount → (2
        : ℕ) * corr.replacementETT.rounds + (11 : ℕ) ≤ (TreeMissingColors sigma
        (corr.replacementETT.series.data.tree (Fin.last
        corr.replacementETT.rounds).castSucc)).card → TreeColorSetMinusClosed G sigma T'
        ((HierarchyTerminalStoredColors K).biUnion (good'.gamma (Fin.last K.dividerCount))) →
    ∀ (a b : Fin k), a ≠ b → a ∈ TreeMissingColors sigma T' → TreeColorSetClosed G sigma T' ({ a }
        : Finset (Fin k)) →
    ∀ (u₁ v₁ u₂ v₂ : V) (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₁) (Sum.inl v₁))
        (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₂) (Sum.inl v₂)), TreeExitPath
        T' sigma a b u₁ v₁ Q₁ → TreeExitPath T' sigma a b u₂ v₂ Q₂ → (
    ∀ x ∈ Q₁.support, x ∉ Q₂.support) → u₁ ≠ u₂ → False) → (0 : ℕ) < H.dividerCount →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount); A = H.stage
        (Fin.last H.dividerCount).castSucc → TreeSequenceInitialSegment A T → (
    ∀ {B C : TreeSequence G e0}, TreeSequenceInitialSegment B C → TreeSequenceVertexSet B ⊆
        TreeSequenceVertexSet C) → TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T →
    ∀ (_ _ _ : Fin (T.length + (1 : ℕ))) (_ : Fin (A.length + (1 : ℕ))), b₁ ∈
        TreeSequenceVertexSet A → b₂ ∈ TreeSequenceVertexSet A → (
    ∀ {f : E} {v w : V}, v ∈ TreeSequenceVertexSet T → w ∉ TreeSequenceVertexSet T → Incident G v
        f → Incident G w f → f ∈ BoundaryEdges G (TreeSequenceVertexSet T)) → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → phi f ≠ some alpha ∧ phi f ≠ some
        theta) →
    let nu : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha theta;
        OutsideKempeRecoloring T phi nu alpha theta → IsProperEdgeColoring G nu →
        IsOneEdgeUncolored nu e0 → StableColoring T (TashkinovStoredColors ett.series.data
        (Fin.last ett.rounds)) phi nu → (
    ∀ (f : E), TreeIncidentEdge T f → nu f = phi f) → (
    ∀ {u : V}, u ∉ TreeSequenceVertexSet T → alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors
        G phi u → theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u) → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good q hlarge
      alpha beta hne a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₁₂ ha₁₂ f₃ _ hinside theta
      hthetaBeta hthetaMissing hthetaClosedStar hnoSmaller hdividerPositive A hAstage hAT
      segmentSubset hsub i₁ i₂ j₃ t₃ hb₁A hb₂A boundaryOfCrossing noBoundary nu hrecolor
      hnuProper hnuOne hnuStable hfixed remoteMissing
  have incidentVertexSupport {u v : V}
      {p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)}
      {f : E} {x : V} (hp : p.IsPath) (hf : Sum.inr f ∈ p.support)
      (hxf : Incident G x f) : Sum.inl x ∈ p.support := by
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hnpos : 0 < n := by
      by_contra h
      have hnzero : n = 0 := by omega
      rw [hnzero] at hn
      simp at hn
    have hnlt : n < p.length := by
      by_contra h
      have hneq : n = p.length := by omega
      rw [hneq] at hn
      simp at hn
    have hprev := p.adj_getVert_succ (i := n - 1) (by omega)
    have hnext := p.adj_getVert_succ (i := n) hnlt
    rw [show n - 1 + 1 = n by omega, hn] at hprev
    rw [hn] at hnext
    cases hpreveq : p.getVert (n - 1) with
    | inr g => rw [hpreveq] at hprev; exact False.elim hprev
    | inl y =>
      rw [hpreveq] at hprev
      cases hnexteq : p.getVert (n + 1) with
      | inr g => rw [hnexteq] at hnext; exact False.elim hnext
      | inl z =>
        rw [hnexteq] at hnext
        have hyz : y ≠ z := by
          intro hyz
          have hverts : p.getVert (n - 1) = p.getVert (n + 1) := by
            rw [hpreveq, hnexteq, hyz]
          have hidx := hp.getVert_injOn
            (show n - 1 ≤ p.length by omega)
            (show n + 1 ≤ p.length by omega) hverts
          omega
        have hends : G.ends f = s(y, z) :=
          (Sym2.mem_and_mem_iff hyz).mp ⟨hprev.1, hnext.1⟩
        have hx : x = y ∨ x = z := by simpa [Incident, hends] using hxf
        rcases hx with rfl | rfl
        · rw [← hpreveq]; exact p.getVert_mem_support _
        · rw [← hnexteq]; exact p.getVert_mem_support _
  have pathBoundary {u v : V}
      (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v))
      (hp : TreeExitPath T phi alpha beta u v p) {f : E}
      (hf : Sum.inr f ∈ p.support) (ht : TreeIncidentEdge T f) :
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    obtain ⟨x, hx, hxf⟩ := ht
    have unique : ∀ y, Incident G y f → y ∈ TreeSequenceVertexSet T → y = v := by
      intro y hyf hy
      exact (hp.2.2.2.2.2 y hy).mp (incidentVertexSupport hp.1 hf hyf)
    obtain ⟨y, z, he⟩ : ∃ y z, G.ends f = s(y, z) := by
      generalize G.ends f = s
      induction s using Sym2.inductionOn with
      | _ y z => exact ⟨y, z, rfl⟩
    have hyf : Incident G y f := by simp [Incident, he]
    have hzf : Incident G z f := by simp [Incident, he]
    have hyz : y ≠ z := by intro h; exact G.loopless f z (by simpa [h] using he)
    have hxends : x = y ∨ x = z := by simpa [Incident, he] using hxf
    rcases hxends with rfl | rfl
    · apply boundaryOfCrossing hx _ hyf hzf
      intro hz
      exact hyz ((unique x hyf hx).trans (unique z hzf hz).symm)
    · apply boundaryOfCrossing hx _ hzf hyf
      intro hy
      exact hyz ((unique y hyf hy).trans (unique x hzf hx).symm)
  have transferExit {u v : V}
      (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v))
      (hp : TreeExitPath T phi alpha beta u v p) (hv : v ∈ TreeSequenceVertexSet A) :
      ∃ Q : (TwoColorIncidenceGraph G nu theta beta).Walk (Sum.inl u) (Sum.inl v),
        TreeExitPath A nu theta beta u v Q ∧ Q.support = p.support := by
    have preserve {w : V} {f : E} (hf : Sum.inr f ∈ p.support)
        (hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl w) (Sum.inr f)) :
        (TwoColorIncidenceGraph G nu theta beta).Adj (Sum.inl w) (Sum.inr f) := by
      refine ⟨hadj.1, ?_⟩
      by_cases ht : TreeIncidentEdge T f
      · have hnot := (noBoundary (pathBoundary p hp hf ht)).1
        exact Or.inr ((hfixed f ht).trans (hadj.2.resolve_left hnot))
      · rcases hadj.2 with ha | hb
        · exact Or.inl (by simp [nu, OutsideTreeColorSwap, ht, ha])
        · exact Or.inr (by simp [nu, OutsideTreeColorSwap, ht, hb,
            hne.symm, hthetaBeta.symm])
    have hedges : ∀ z, z ∈ p.edges →
        z ∈ (TwoColorIncidenceGraph G nu theta beta).edgeSet := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
        have hadj := (SimpleGraph.mem_edgeSet _).mp (p.edges_subset_edgeSet hz)
        have hx := p.fst_mem_support_of_mem_edges hz
        have hy := p.snd_mem_support_of_mem_edges hz
        apply (SimpleGraph.mem_edgeSet _).mpr
        cases x <;> cases y
        · exact hadj.elim
        · exact preserve hy hadj
        · exact (preserve hx hadj.symm).symm
        · exact hadj.elim
    let Q := p.transfer (TwoColorIncidenceGraph G nu theta beta) hedges
    refine ⟨Q, ⟨hp.1.transfer hedges, ?_, ?_, hv,
      remoteMissing hp.2.2.1 hp.2.2.2.2.1, ?_⟩, by simp [Q]⟩
    · simpa [Q] using hp.2.1
    · intro hu; exact hp.2.2.1 (hsub hu)
    · intro w hw
      simpa [Q] using hp.2.2.2.2.2 w (hsub hw)
  obtain ⟨Q₁, hQ₁, hsQ₁⟩ := transferExit P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, hsQ₂⟩ := transferExit P₂ hP₂ hb₂A
  obtain ⟨Q₃, hQ₃, hsQ₃⟩ := transferExit P₃ hP₃ hinside
  have ladderSub : TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
        TreeSequenceVertexSet T := segmentSubset ett.abovePenultimate
  have hstableLadder : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi nu := by
    constructor
    · intro f hf hc
      obtain ⟨v, hv, hvf⟩ := hf
      exact hfixed f ⟨v, ladderSub hv, hvf⟩
    · intro v hv
      exact hnuStable.2 v (ladderSub hv)
  have treeMissingFixed {B : TreeSequence G e0}
      (hB : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet T) :
      TreeMissingColors nu B = TreeMissingColors phi B := by
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hnuStable.2 v (hB hv)
  have hthetaNu : theta ∈ TreeMissingColors nu A := by
    rw [treeMissingFixed hsub]
    exact hthetaMissing
  have hthetaClosedNu : TreeColorSetClosed G nu A {theta} := by
    intro c hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet A) :=
      (Finset.mem_filter.mp hf).1
    have hfc : nu f = some c := (Finset.mem_filter.mp hf).2
    have hcross : ∃ v ∈ TreeSequenceVertexSet A,
        ∃ w ∉ TreeSequenceVertexSet A, G.ends f = s(v, w) :=
      by simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hfb
    obtain ⟨v, hv, w, hw, he⟩ := hcross
    have hvf : Incident G v f := by simp [Incident, he]
    have hold : phi f = some c := (hfixed f ⟨v, hsub hv, hvf⟩).symm.trans hfc
    have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet A) c :=
      Finset.mem_filter.mpr ⟨hfb, hold⟩
    rw [hthetaClosedStar c hc] at hm
    simp at hm
  obtain ⟨_, _, _, _, corrNu, hMPNu, baseNu, HNu, goodNu, hsame, hterminalNu⟩ :=
    HierarchyLEMStable G k e0 input T phi nu ett hMP hpositive hlower base H good
      hproper hone alpha theta hrecolor
  have hcount : H.dividerCount = HNu.dividerCount := hsame.1.2.1
  exact @helper_continuation_355 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@base) (@H) (@good)
      (@hlarge) (@alpha) (@beta) (@a₁) (@b₁) (@a₂) (@b₂) (@P₁) (@P₂) (@hpaths₁₂) (@ha₁₂) (@theta)
      (@hthetaBeta) (@hnoSmaller) (@hdividerPositive) (@hAstage) (@hnuProper) (@hnuOne) (@Q₁)
      (@hQ₁) (@hsQ₁) (@Q₂) (@hQ₂) (@hsQ₂) (@ladderSub) (@hstableLadder) (@treeMissingFixed)
      (@hthetaNu) (@hthetaClosedNu) (@corrNu) (@hMPNu) (@baseNu) (@HNu) (@goodNu) (@hsame) (@hcount)
lemma Step1CaseTwoInsidePositiveDivider {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (_ : H.dividerCount < q)
    (_ : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (_ : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (_ : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (_ : beta ∉ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (hpaths₁₂ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (_ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (_ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (ha₁₂ : a₁ ≠ a₂) (_ : a₁ ≠ a₃) (_ : a₂ ≠ a₃)
    (_ : b₁ ≠ b₂) (_ : b₁ ≠ b₃) (_ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (_ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : Incident G b₁ f₁) (_ : Incident G b₂ f₂)
    (_ : Incident G b₃ f₃)
    (_ : Sum.inr f₁ ∈ P₁.support)
    (_ : Sum.inr f₂ ∈ P₂.support)
    (_ : Sum.inr f₃ ∈ P₃.support)
    (hinside : b₃ ∈ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (theta : Fin k) (hthetaAlpha : theta ≠ alpha)
    (hthetaBeta : theta ≠ beta)
    (hthetaMissing : theta ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hthetaClosedStar : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {theta})
    (hthetaClosed : TreeColorSetClosed G phi T {theta})
    (hnoSmaller :
      ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T'),
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
          phi sigma →
        MaximumProperty corr.replacementETT →
        ∀ (base' : HierarchyBase corr.replacementETT sigma)
          (K : TashkinovHierarchy corr.replacementETT base')
          (good' : GoodHierarchy K),
          K.dividerCount < H.dividerCount →
          2 * corr.replacementETT.rounds + 11 ≤
            (TreeMissingColors sigma
              (corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc)).card →
          TreeColorSetMinusClosed G sigma T'
            ((HierarchyTerminalStoredColors K).biUnion
              (good'.gamma (Fin.last K.dividerCount))) →
          ∀ (a b : Fin k), a ≠ b →
            a ∈ TreeMissingColors sigma T' →
            TreeColorSetClosed G sigma T' {a} →
            ∀ (u₁ v₁ u₂ v₂ : V)
              (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₁) (Sum.inl v₁))
              (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₂) (Sum.inl v₂)),
              TreeExitPath T' sigma a b u₁ v₁ Q₁ →
              TreeExitPath T' sigma a b u₂ v₂ Q₂ →
              (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
              u₁ ≠ u₂ → False)
    (hdividerPositive : 0 < H.dividerCount) : False := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hAstage : A = H.stage (Fin.last H.dividerCount).castSucc := by
    let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hi : i.succ = Fin.last H.dividerCount := by
      apply Fin.ext
      simp [i]
      omega
    dsimp [A]
    rw [← hi]
    simp [HierarchyStarredStage]
  have hAT : TreeSequenceInitialSegment A T := by
    let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hi : (Fin.last H.dividerCount).castSucc =
        (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) := by
      apply Fin.ext
      simp [i]
      omega
    rw [hAstage]
    rw [hi, H.dividerStage i]
    exact ⟨Nat.le_of_lt_succ (H.dividerPosition i).isLt,
      by intro j; rfl, by intro j; rfl⟩
  have segmentSubset {B C : TreeSequence G e0}
      (hs : TreeSequenceInitialSegment B C) :
      TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet C := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨Fin.castLE (Nat.succ_le_succ hs.1) i, hs.2.1 i⟩
  have hsub := segmentSubset hAT
  obtain ⟨i₁, i₂, hi₁, hi₂, hi₁₂⟩ := horder₁₂
  obtain ⟨j₂, j₃, hj₂, hj₃, hj₂₃⟩ := horder₂₃
  have hj₂eq : j₂ = i₂ := T.vertex_injective (hj₂.trans hi₂.symm)
  subst j₂
  obtain ⟨t₃, ht₃⟩ : ∃ t : Fin (A.length + 1), A.vertex t = b₃ := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] using hinside
  have ht₃eq : Fin.castLE (Nat.succ_le_succ hAT.1) t₃ = j₃ :=
    T.vertex_injective ((hAT.2.1 t₃).trans (ht₃.trans hj₃.symm))
  have hj₃bound : j₃.val ≤ A.length := by
    rw [← ht₃eq]
    exact Nat.le_of_lt_succ t₃.isLt
  have hb₁A : b₁ ∈ TreeSequenceVertexSet A := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    let t : Fin (A.length + 1) := ⟨i₁.val, by omega⟩
    refine ⟨t, ?_⟩
    have ht : Fin.castLE (Nat.succ_le_succ hAT.1) t = i₁ := Fin.ext rfl
    exact (hAT.2.1 t).symm.trans (ht ▸ hi₁)
  have hb₂A : b₂ ∈ TreeSequenceVertexSet A := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    let t : Fin (A.length + 1) := ⟨i₂.val, by omega⟩
    refine ⟨t, ?_⟩
    have ht : Fin.castLE (Nat.succ_le_succ hAT.1) t = i₂ := Fin.ext rfl
    exact (hAT.2.1 t).symm.trans (ht ▸ hi₂)
  have boundaryOfCrossing {f : E} {v w : V}
      (hv : v ∈ TreeSequenceVertexSet T) (hw : w ∉ TreeSequenceVertexSet T)
      (hvf : Incident G v f) (hwf : Incident G w f) :
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    have hvw : v ≠ w := by intro h; exact hw (h ▸ hv)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, w, hw, (Sym2.mem_and_mem_iff hvw).mp ⟨hvf, hwf⟩⟩
  have noBoundary {f : E} (hf : f ∈ BoundaryEdges G (TreeSequenceVertexSet T)) :
      phi f ≠ some alpha ∧ phi f ≠ some theta := by
    constructor
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha := by
        simp [BoundaryColorEdges, hf, hc]
      rw [hclosed alpha (by simp)] at hm
      simp at hm
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) theta := by
        simp [BoundaryColorEdges, hf, hc]
      rw [hthetaClosed theta (by simp)] at hm
      simp at hm
  let Outside : Sum V E → Prop
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr f => ¬ TreeIncidentEdge T f
  have outsideStep {x y : Sum V E}
      (hxy : (TwoColorIncidenceGraph G phi alpha theta).Adj x y)
      (hx : Outside x) : Outside y := by
    cases x with
    | inl v =>
      cases y with
      | inl w => exact False.elim hxy
      | inr f =>
        rintro ⟨w, hw, hwf⟩
        have hf := boundaryOfCrossing hw hx hwf hxy.1
        rcases hxy.2 with ha | ht
        · exact (noBoundary hf).1 ha
        · exact (noBoundary hf).2 ht
    | inr f =>
      cases y with
      | inr g => exact False.elim hxy
      | inl v => intro hv; exact hx ⟨v, hv, hxy.1⟩
  have outsideComponent {z x : Sum V E} (hz : Outside z)
      (hx : x ∈ TwoColorComponent G phi alpha theta z) : Outside x := by
    have hr : (TwoColorIncidenceGraph G phi alpha theta).Reachable z x := by
      apply SimpleGraph.ConnectedComponent.exact
      change (TwoColorIncidenceGraph G phi alpha theta).connectedComponentMk x =
        (TwoColorIncidenceGraph G phi alpha theta).connectedComponentMk z at hx
      exact hx.symm
    clear hx
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    induction hr with
    | refl => exact hz
    | tail hr hlast ih => exact outsideStep hlast ih
  let roots : Finset (Sum V E) := Finset.univ.filter Outside
  have selected {f : E} :
      (∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z) ↔
        ¬ TreeIncidentEdge T f := by
    constructor
    · rintro ⟨z, hz, hf⟩
      exact outsideComponent (Finset.mem_filter.mp hz).2 hf
    · intro hf
      refine ⟨Sum.inr f, by simp [roots, Outside, hf], ?_⟩
      change (TwoColorIncidenceGraph G phi alpha theta).connectedComponentMk
          (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha theta).connectedComponentMk
          (Sum.inr f)
      rfl
  let nu := OutsideTreeColorSwap T phi alpha theta
  have hrecolor : OutsideKempeRecoloring T phi nu alpha theta := by
    refine ⟨hthetaAlpha.symm, roots, ?_, ?_⟩
    · intro z hz v hv
      exact outsideComponent (Finset.mem_filter.mp hz).2 hv
    · intro f
      by_cases hf : TreeIncidentEdge T f <;>
        simp [nu, OutsideTreeColorSwap, selected, hf]
  obtain ⟨hnuProper, hnuOne, hnuStable, hnuInvariant, hfixed⟩ :=
    OutsideKempeRecoloringStable G e0 T
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi nu alpha theta hproper hone hrecolor
  have missingIff (p : PartialEdgeColoring E k) (v : V) (c : Fin k) :
      c ∈ MissingColors G p v ↔ ∀ f, Incident G v f → p f ≠ some c := by
    simp [MissingColors, PresentColors]
  have remoteMissing {u : V} (hu : u ∉ TreeSequenceVertexSet T)
      (hm : alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) :
      theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u := by
    rcases hm with hm | hm
    · left
      apply (missingIff nu u theta).mpr
      intro f huf hnew
      by_cases ht : TreeIncidentEdge T f
      · obtain ⟨v, hv, hvf⟩ := ht
        exact (noBoundary (boundaryOfCrossing hv hu hvf huf)).2
          ((hfixed f ⟨v, hv, hvf⟩).symm.trans hnew)
      · have hfa := (missingIff phi u alpha).mp hm f huf
        by_cases hft : phi f = some theta
        · have heq : alpha = theta := by
            simpa [nu, OutsideTreeColorSwap, ht, hfa, hft, hthetaAlpha] using hnew
          exact hthetaAlpha heq.symm
        · exact hft (by simp [nu, OutsideTreeColorSwap, ht, hfa, hft] at hnew)
    · right
      apply (missingIff nu u beta).mpr
      intro f huf hnew
      apply (missingIff phi u beta).mp hm f huf
      by_cases ht : TreeIncidentEdge T f
      · exact (hfixed f ht).symm.trans hnew
      · by_cases hfa : phi f = some alpha
        · have heq : theta = beta := by
            simpa [nu, OutsideTreeColorSwap, ht, hfa] using hnew
          exact False.elim (hthetaBeta heq)
        · by_cases hft : phi f = some theta
          · have heq : alpha = beta := by
              simpa [nu, OutsideTreeColorSwap, ht, hfa, hft, hthetaAlpha] using hnew
            exact False.elim (hne heq)
          · simpa [nu, OutsideTreeColorSwap, ht, hfa, hft] using hnew
  exact @helper_continuation_361 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hMP) (@hpositive) (@hproper)
      (@hone) (@hlower) (@base) (@H) (@good) (@q) (@hlarge) (@alpha) (@beta) (@hne) (@a₁) (@b₁)
      (@a₂) (@b₂) (@a₃) (@b₃) (@P₁) (@P₂) (@P₃) (@hP₁) (@hP₂) (@hP₃) (@hpaths₁₂) (@ha₁₂) (@f₃)
      (by assumption) (@hinside) (@theta) (@hthetaBeta) (@hthetaMissing) (@hthetaClosedStar)
      (@hnoSmaller) (@hdividerPositive) (@hAstage) (@hAT) (@segmentSubset) (@hsub) (@i₁) (@i₂)
      (@j₃) (@t₃) (@hb₁A) (@hb₂A) (@boundaryOfCrossing) (@noBoundary) (@hrecolor) (@hnuProper)
      (@hnuOne) (@hnuStable) (@hfixed) (@remoteMissing)
end GoldbergSeymour

end
