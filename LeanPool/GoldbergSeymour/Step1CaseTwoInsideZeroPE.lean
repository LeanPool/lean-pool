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
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
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
public import LeanPool.GoldbergSeymour.Step1ZeroDividerAnchorPE
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Case Two Inside Zero PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_382.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    MaximumProperty ett →
    (0 : ℕ) < ett.rounds →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : GoodHierarchy H) (alpha beta : Fin k) (a₁ b₁ a₂ b₂ a₃ b₃ : V)
      (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁) (Sum.inl b₁))
      (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl b₂))
      (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
    TreeExitPath T phi alpha beta a₁ b₁ P₁ →
    TreeExitPath T phi alpha beta a₂ b₂ P₂ →
    TreeExitPath T phi alpha beta a₃ b₃ P₃ →
    (∀ x ∈ P₂.support, x ∉ P₃.support) →
    a₂ ≠ a₃ →
    ∀ (theta : Fin k),
    theta ≠ beta →
    theta ∈ TreeMissingColors phi (HierarchyStarredStage H (Fin.last H.dividerCount)) →
    TreeColorSetClosed G phi (HierarchyStarredStage H (Fin.last H.dividerCount))
        ({ theta } : Finset (Fin k)) →
    (∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T'),
        IsProperEdgeColoring G sigma →
          IsOneEdgeUncolored sigma e0 →
            StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma →
              MaximumProperty corr.replacementETT →
                ∀ (base' : HierarchyBase corr.replacementETT sigma)
                  (K : TashkinovHierarchy corr.replacementETT base')
                  (good' : GoodHierarchy K),
                  K.dividerCount < H.dividerCount →
                    (2 : ℕ) * corr.replacementETT.rounds + (11 : ℕ) ≤
                        (TreeMissingColors sigma
                            (corr.replacementETT.series.data.tree
                              (Fin.last corr.replacementETT.rounds).castSucc)).card →
                      TreeColorSetMinusClosed G sigma T'
                          ((HierarchyTerminalStoredColors K).biUnion
                            (good'.gamma (Fin.last K.dividerCount))) →
                        ∀ (a b : Fin k),
                          a ≠ b →
                            a ∈ TreeMissingColors sigma T' →
                              TreeColorSetClosed G sigma T' ({ a } : Finset (Fin k)) →
                                ∀ (u₁ v₁ u₂ v₂ : V)
                                  (Q₁ :
                                    (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₁)
                                      (Sum.inl v₁))
                                  (Q₂ :
                                    (TwoColorIncidenceGraph G sigma a b).Walk (Sum.inl u₂)
                                      (Sum.inl v₂)),
                                  TreeExitPath T' sigma a b u₁ v₁ Q₁ →
                                    TreeExitPath T' sigma a b u₂ v₂ Q₂ →
                                      (∀ x ∈ Q₁.support, x ∉ Q₂.support) →
                                        u₁ ≠ u₂ → False) →
    H.dividerCount = (0 : ℕ) →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    A = base.core →
    TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T →
    b₃ ∈ TreeSequenceVertexSet A →
    b₂ ∈ TreeSequenceVertexSet A →
    b₁ ∈ TreeSequenceVertexSet A →
    let roots : Finset (V ⊕ E) :=
      ({z : V ⊕ E |
          match z with
          | Sum.inl v => v ∉ TreeSequenceVertexSet T
          | Sum.inr _ => False} :
        Finset (V ⊕ E));
    let selected : E → Prop := fun (f : E) ↦
      ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z;
    let nu : PartialEdgeColoring E k := fun (f : E) ↦
      if selected f then
        if phi f = some alpha then some theta
        else if phi f = some theta then some alpha else phi f
      else phi f;
    OutsideKempeRecoloring T phi nu alpha theta →
    (∀ u ∉ TreeSequenceVertexSet T,
        ∀ (f : E), Incident G u f → phi f = some alpha ∨ phi f = some theta → selected f) →
    (∀ (f : E), nu f = some beta ↔ phi f = some beta) →
    (∀ u ∉ TreeSequenceVertexSet T,
        alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u →
          theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u) →
    (∀ (u v : V)
        (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath T phi alpha beta u v P →
          ∀ (f : E),
            Sum.inr f ∈ P.support → ∃ w ∉ TreeSequenceVertexSet T, Incident G w f) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good alpha
      beta a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₂₃ ha₂₃ theta hthetaBeta hthetaMissing
      hthetaClosedStar _ hdividerZero hPE A hAcore hAsub hb₃A hb₂A hb₁A roots selected nu
      hrecolor selectedOfOutside betaFixed remoteMissing pathEdgeOutside
  have transferExit : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P → v ∈ TreeSequenceVertexSet A →
      ∃ Q : (TwoColorIncidenceGraph G nu theta beta).Walk
          (Sum.inl u) (Sum.inl v),
        TreeExitPath A nu theta beta u v Q ∧ Q.support = P.support := by
    intro u v P hExit hvA
    have colors : ∀ f, Sum.inr f ∈ P.support →
        (phi f = some alpha ∨ phi f = some beta) →
        nu f = some theta ∨ nu f = some beta := by
      intro f hf hc
      rcases hc with ha | hb
      · obtain ⟨w, hwT, hwf⟩ := pathEdgeOutside u v P hExit f hf
        have hs := selectedOfOutside w hwT f hwf (Or.inl ha)
        exact Or.inl (by simp [nu, hs, ha])
      · exact Or.inr ((betaFixed f).mpr hb)
    have edges : ∀ z, z ∈ P.edges → z ∈ (TwoColorIncidenceGraph G nu theta beta).edgeSet := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
          have hadj := (SimpleGraph.mem_edgeSet _).mp (P.edges_subset_edgeSet hz)
          have hx := P.fst_mem_support_of_mem_edges hz
          have hy := P.snd_mem_support_of_mem_edges hz
          apply (SimpleGraph.mem_edgeSet _).mpr
          cases x with
          | inl w =>
              cases y with
              | inl z => exact False.elim hadj
              | inr f => exact ⟨hadj.1, colors f hy hadj.2⟩
          | inr f =>
              cases y with
              | inr g => exact False.elim hadj
              | inl w => exact ⟨hadj.1, colors f hx hadj.2⟩
    let Q := P.transfer (TwoColorIncidenceGraph G nu theta beta) edges
    refine ⟨Q, ?_, by simp [Q]⟩
    refine ⟨hExit.1.transfer edges, by simpa [Q] using hExit.2.1,
      fun huA => hExit.2.2.1 (hAsub huA), hvA,
      remoteMissing u hExit.2.2.1 hExit.2.2.2.2.1, ?_⟩
    intro w hw
    simpa [Q] using hExit.2.2.2.2.2 w (hAsub hw)
  obtain ⟨Q₁, hQ₁, hs₁⟩ := transferExit a₁ b₁ P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, hs₂⟩ := transferExit a₂ b₂ P₂ hP₂ hb₂A
  obtain ⟨Q₃, hQ₃, hs₃⟩ := transferExit a₃ b₃ P₃ hP₃ hb₃A
  obtain ⟨hnuProper, hnuOne, hnuStable, hnuInvariant,
    corr, hnuMP, baseNu, K, goodNu, hsame, _⟩ :=
    HierarchyLEMStable G k e0 input T phi nu ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  have hfixed := (OutsideKempeRecoloringStable G e0 T ∅ phi nu alpha theta
    hproper hone hrecolor).2.2.2.2
  rcases hsame.1 with ⟨hcore, hcount, _, _, hkind, _⟩
  have hKzero : K.dividerCount = 0 := hcount.symm.trans hdividerZero
  have hKlast : Fin.last K.dividerCount = (0 : Fin (K.dividerCount + 1)) :=
    Fin.ext (by simp [hKzero])
  have hKcore : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
    rw [hKlast]
    change baseNu.core = A
    exact hcore.symm.trans hAcore.symm
  have hthetaNu : theta ∈ TreeMissingColors nu A := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hthetaMissing
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, ?_⟩
    rw [hnuInvariant.2 v (hAsub hv)]
    exact hm
  have hthetaNuClosed : TreeColorSetClosed G nu A {theta} := by
    intro c hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet A) ∧
        nu f = some c := by simpa [BoundaryColorEdges] using hf
    obtain ⟨u, hu, v, hv, he⟩ := by
      simpa [BoundaryEdges] using hboundary.1
    have huf : Incident G u f := by simp [Incident, he]
    have hold : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet A) c := by
      apply Finset.mem_filter.mpr
      exact ⟨hboundary.1, (hfixed f ⟨u, hAsub hu, huf⟩).symm.trans hboundary.2⟩
    rw [hthetaClosedStar c hc] at hold
    exact Finset.notMem_empty _ hold
  -- The closed PE anchor performs the second exchange on this transported base.
  apply Step1ZeroDividerAnchorPE G k e0 corr.replacementInput T nu
    corr.replacementETT hnuMP (by simpa [corr.rungAgreement] using hpositive)
    hnuProper hnuOne (fun lower hp hr hm =>
      hlower lower hp (by simpa [corr.rungAgreement] using hr) hm)
    baseNu K hKzero theta beta hthetaBeta
    (by simpa only [hKcore] using hthetaNu)
    (by simpa only [hKcore] using hthetaNuClosed)
    a₂ b₂ a₃ b₃ Q₂ Q₃
    (by simpa only [hKcore] using hQ₂)
    (by simpa only [hKcore] using hQ₃)
    (fun z hz => by rw [hs₂] at hz; rw [hs₃]; exact hpaths₂₃ z hz)
    ha₂₃ (hkind.mp hPE)

lemma Step1CaseTwoInsideZeroPE {V E : Type*}
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
    (_ : 2 * ett.rounds + 11 ≤
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
    (_ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (_ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (_ : a₁ ≠ a₂) (_ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
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
    (_ :
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
    (hdividerZero : H.dividerCount = 0)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
    False := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hlast : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
    Fin.ext (by simp [hdividerZero])
  have hAcore : A = base.core := by
    simp [A, hlast, HierarchyStarredStage]
  have hfirst : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
      Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hdividerZero])
  have hAT : TreeSequenceInitialSegment A T := by
    simpa only [hAcore, hfirst, H.terminalStage] using H.coreInsideFirst
  have hAsub := TreeSequenceInitialSegmentVertexSetSubset hAT
  have beforeInside : ∀ {u v : V}, TreeVertexOrder T u v →
      v ∈ TreeSequenceVertexSet A → u ∈ TreeSequenceVertexSet A := by
    intro u v huv hv
    obtain ⟨i, j, hi, hj, hij⟩ := huv
    obtain ⟨r, hr⟩ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and] using hv
    have hrj : Fin.castLE (Nat.succ_le_succ hAT.1) r = j :=
      T.vertex_injective ((hAT.2.1 r).trans (hr.trans hj.symm))
    have hval : r.val = j.val := congrArg Fin.val hrj
    let s : Fin (A.length + 1) := ⟨i.val, by have := r.isLt; omega⟩
    have hsi : Fin.castLE (Nat.succ_le_succ hAT.1) s = i := Fin.ext rfl
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨s, (hAT.2.1 s).symm.trans (hsi ▸ hi)⟩
  have hb₃A : b₃ ∈ TreeSequenceVertexSet A := hinside
  have hb₂A := beforeInside horder₂₃ hb₃A
  have hb₁A := beforeInside horder₁₂ hb₂A
  have noBoundary : ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f ≠ some alpha ∧ phi f ≠ some theta := by
    intro f hf
    constructor
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hclosed alpha (by simp)] at hm
      exact Finset.notMem_empty _ hm
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) theta :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hthetaClosed theta (by simp)] at hm
      exact Finset.notMem_empty _ hm
  have boundaryOfOutside : ∀ {v : V} {f : E},
      v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro v f hv hvf ⟨w, hw, hwf⟩
    have hwv : w ≠ v := by intro h; exact hv (h ▸ hw)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, v, hv, (Sym2.mem_and_mem_iff hwv).mp ⟨hwf, hvf⟩⟩
  let J := TwoColorIncidenceGraph G phi alpha theta
  let S : Set (Sum V E) := {z | match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr f => ¬ TreeIncidentEdge T f}
  have outsideStep : ∀ z, z ∈ S → ∀ w, J.Adj z w → w ∈ S := by
    intro z hz w hzw
    cases z with
    | inl v =>
        cases w with
        | inl u => exact False.elim hzw
        | inr f =>
            intro hfT
            have hb := noBoundary (boundaryOfOutside hz hzw.1 hfT)
            exact hzw.2.elim hb.1 hb.2
    | inr f =>
        cases w with
        | inr g => exact False.elim hzw
        | inl v => exact fun hv => hz ⟨v, hv, hzw.1⟩
  let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
    match z with
    | Sum.inl v => v ∉ TreeSequenceVertexSet T
    | Sum.inr _ => False
  let selected : E → Prop := fun f =>
    ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha theta z
  let nu : PartialEdgeColoring E k := fun f =>
    if selected f then
      if phi f = some alpha then some theta
      else if phi f = some theta then some alpha else phi f
    else phi f
  have outsideComponents : ∀ z ∈ roots, ∀ v : V,
      Sum.inl v ∈ TwoColorComponent G phi alpha theta z →
      v ∉ TreeSequenceVertexSet T := by
    intro z hz v hv
    have hzS : z ∈ S := by
      cases z with
      | inl vertex =>
          simpa only [roots, S, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
              using hz
      | inr edge => simp [roots] at hz
    have hr : J.Reachable z (Sum.inl v) := by
      change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk z at hv
      exact (SimpleGraph.ConnectedComponent.eq.mp hv).symm
    exact hr.mem_subgraphVerts
      (H := (⊤ : J.Subgraph).induce S)
      (fun x hx y hxy => ⟨hx, outsideStep x hx y hxy, hxy⟩) hzS
  have hrecolor : OutsideKempeRecoloring T phi nu alpha theta :=
    ⟨hthetaAlpha.symm, roots, outsideComponents, fun _ => rfl⟩
  have selectedOfOutside : ∀ (u : V), u ∉ TreeSequenceVertexSet T →
      ∀ (f : E), Incident G u f →
      (phi f = some alpha ∨ phi f = some theta) → selected f := by
    intro u hu f huf hcolor
    refine ⟨Sum.inl u, by simp [roots, hu], ?_⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (show J.Adj (Sum.inl u) (Sum.inr f) from ⟨huf, hcolor⟩)).symm
  have betaFixed : ∀ f : E, nu f = some beta ↔ phi f = some beta := by
    intro f
    by_cases hs : selected f <;> by_cases ha : phi f = some alpha <;>
      by_cases ht : phi f = some theta <;>
      simp [nu, hs, ha, ht, hne, hthetaBeta, hthetaAlpha]
  have thetaPreimage : ∀ (u : V), u ∉ TreeSequenceVertexSet T →
      ∀ (f : E), Incident G u f →
      (nu f = some theta ↔ phi f = some alpha) := by
    intro u hu f huf
    by_cases ha : phi f = some alpha
    · have hs := selectedOfOutside u hu f huf (Or.inl ha)
      simp [nu, hs, ha]
    · by_cases ht : phi f = some theta
      · have hs := selectedOfOutside u hu f huf (Or.inr ht)
        simp [nu, hs, ht, hthetaAlpha.symm]
      · by_cases hs : selected f <;> simp [nu, hs, ha, ht]
  have missingIff : ∀ (p : PartialEdgeColoring E k) (v : V) (c : Fin k),
      c ∈ MissingColors G p v ↔ ∀ f, Incident G v f → p f ≠ some c := by
    intro p v c
    simp [MissingColors, PresentColors]
  have remoteMissing : ∀ u, u ∉ TreeSequenceVertexSet T →
      (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) →
      theta ∈ MissingColors G nu u ∨ beta ∈ MissingColors G nu u := by
    intro u hu hm
    rcases hm with hm | hm
    · left
      apply (missingIff nu u theta).mpr
      intro f huf hf
      exact (missingIff phi u alpha).mp hm f huf
        ((thetaPreimage u hu f huf).mp hf)
    · right
      apply (missingIff nu u beta).mpr
      intro f huf hf
      exact (missingIff phi u beta).mp hm f huf ((betaFixed f).mp hf)
  have pathEdgeOutside : ∀ (u v : V)
      (P : (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl u) (Sum.inl v)),
      TreeExitPath T phi alpha beta u v P →
      ∀ f : E, Sum.inr f ∈ P.support →
        ∃ w : V, w ∉ TreeSequenceVertexSet T ∧ Incident G w f := by
    intro u v P hExit f hf
    obtain ⟨m, hm, hmle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hmpos : 0 < m := by
      by_contra h
      have hmzero : m = 0 := by omega
      rw [hmzero] at hm
      simp at hm
    have hmlt : m < P.length := by
      by_contra h
      have hmlast : m = P.length := by omega
      rw [hmlast] at hm
      simp at hm
    have hprev := P.adj_getVert_succ (i := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, hm] at hprev
    obtain ⟨w, hwPrev⟩ : ∃ w : V, P.getVert (m - 1) = Sum.inl w := by
      cases hnode : P.getVert (m - 1) with
      | inl w => exact ⟨w, rfl⟩
      | inr e => rw [hnode] at hprev; exact False.elim hprev
    have hnext := P.adj_getVert_succ (i := m) hmlt
    rw [hm] at hnext
    obtain ⟨z, hzNext⟩ : ∃ z : V, P.getVert (m + 1) = Sum.inl z := by
      cases hnode : P.getVert (m + 1) with
      | inl z => exact ⟨z, rfl⟩
      | inr e => rw [hnode] at hnext; exact False.elim hnext
    rw [hwPrev] at hprev
    rw [hzNext] at hnext
    by_cases hwT : w ∈ TreeSequenceVertexSet T
    · by_cases hzT : z ∈ TreeSequenceVertexSet T
      · have hwv : w = v := (hExit.2.2.2.2.2 w hwT).mp (by
          rw [← hwPrev]; exact P.getVert_mem_support _)
        have hzv : z = v := (hExit.2.2.2.2.2 z hzT).mp (by
          rw [← hzNext]; exact P.getVert_mem_support _)
        have heq : P.getVert (m - 1) = P.getVert (m + 1) := by
          rw [hwPrev, hzNext, hwv, hzv]
        have hindices := hExit.1.getVert_injOn
          (show m - 1 ≤ P.length by omega) (show m + 1 ≤ P.length by omega) heq
        omega
      · exact ⟨z, hzT, hnext.1⟩
    · exact ⟨w, hwT, hprev.1⟩
  exact @helper_continuation_382 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hMP) (@hpositive) (@hproper)
      (@hone) (@hlower) (@base) (@H) (@good) (@alpha) (@beta) (@a₁) (@b₁) (@a₂) (@b₂) (@a₃) (@b₃)
      (@P₁) (@P₂) (@P₃) (@hP₁) (@hP₂) (@hP₃) (@hpaths₂₃) (@ha₂₃) (@theta) (@hthetaBeta)
      (@hthetaMissing) (@hthetaClosedStar) (by assumption) (@hdividerZero) (@hPE) (@hAcore)
      (@hAsub) (@hb₃A) (@hb₂A) (@hb₁A) (@hrecolor) (@selectedOfOutside) (@betaFixed)
      (@remoteMissing) (@pathEdgeOutside)
end GoldbergSeymour

end
