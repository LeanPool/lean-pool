/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryColorVertex
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.DefectiveColor
public import LeanPool.GoldbergSeymour.DefectiveVertex
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
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
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeExitPath
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
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.Step1CaseTwoOutsidePrefixHierarchy
public import LeanPool.GoldbergSeymour.Step1CaseTwoOutsideRecoloredPrefix
public import LeanPool.GoldbergSeymour.Step1CaseTwoOutsideTwoEdgeExtension

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Case Two Outside Prefix Two Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1CaseTwoOutsidePrefixTwoEdges {V E : Type*}
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
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (halpha : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∉ TreeMissingColors phi T)
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
    (hpaths₁₃ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₃ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hif₃ : Incident G b₃ f₃)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hPf₃ : Sum.inr f₃ ∈ P₃.support)
    (houtside : b₃ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))) :
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k) (C J₁ J : TreeSequence G e0) (corrJ :
      CorrespondingExtendedTashkinovTree G k e0 ett mu J) (baseJ :
      HierarchyBase corrJ.replacementETT mu) (KJ :
      TashkinovHierarchy corrJ.replacementETT baseJ) (goodJ : GoodHierarchy KJ) (R₁ :
      (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₁) (Sum.inl b₁)) (R₂ :
      (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)) (R₃ :
      (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
    gamma ≠ beta ∧
      IsProperEdgeColoring G mu ∧
        IsOneEdgeUncolored mu e0 ∧
          StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi mu ∧
            ModColoring ett mu ∧
              MaximumProperty corrJ.replacementETT ∧
                KJ.dividerCount = H.dividerCount ∧
                  2 * corrJ.replacementETT.rounds + 11 ≤
                      (TreeMissingColors mu
                          (corrJ.replacementETT.series.data.tree
                            (Fin.last corrJ.replacementETT.rounds).castSucc)).card ∧
                    gamma ∉
                        (HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount)).biUnion
                          (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
                      beta ∉
                          (HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount)).biUnion
                            (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
                        beta ∈ MissingColors G mu b₃ ∧
                          TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧
                            TreeExitPath T mu gamma beta a₂ b₂ R₂ ∧
                              TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧
                                (∀ x, x ∈ R₁.support → x ∉ R₂.support) ∧
                                  (∀ x, x ∈ R₁.support → x ∉ R₃.support) ∧
                                    (∀ x, x ∈ R₂.support → x ∉ R₃.support) ∧
                                      R₁.support = P₁.support ∧
                                        R₂.support = P₂.support ∧
                                          R₃.support = P₃.support ∧
                                            R₁.length = P₁.length ∧
                                              R₂.length = P₂.length ∧
                                                R₃.length = P₃.length ∧
                                                  TreeSequenceInitialSegment C T ∧
                                                    C.vertex (Fin.last C.length) = b₃ ∧
                                                      TreeSequenceAdjoinEdge C f₁ J₁ ∧
                                                        TreeSequenceAdjoinEdge J₁ f₂ J ∧
                                                          (∀ v,
                                                              Incident G v f₁ →
                                                                v ∈
                                                                  TreeSequenceVertexSet J) ∧
                                                            (∀ v,
                                                                Incident G v f₂ →
                                                                  v ∈
                                                                    TreeSequenceVertexSet
                                                                      J) ∧
                                                              b₁ ∈ TreeSequenceVertexSet J ∧
                                                                b₂ ∈
                                                                    TreeSequenceVertexSet
                                                                      J ∧
                                                                  b₃ ∈
                                                                    TreeSequenceVertexSet J := by
  obtain ⟨gamma, mu, Bminus, C, R₁, R₂, R₃, hgamma, hproperMu, honeMu,
    hstable, hfixed, hmissingFixed, hreserved, hgammaMissing, hbetaMissing,
    hcolor, hotherMissing, hR₁, hR₂, hR₃, hd₁₂, hd₁₃, hd₂₃, hs₁, hs₂, hs₃,
    hl₁, hl₂, hl₃, hAB, hBCstrict, hCT, hlast, hadjoin, hf₁mu, hf₂mu,
    houtDistinct, hb₁C, hb₂C, hb₃C⟩ :=
    Step1CaseTwoOutsideRecoloredPrefix G k e0 input T phi ett hproper hone
      base H good hterminal hElementary alpha beta halpha hclosed hne hbeta
      a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃
      hpaths₂₃ ha₁₂ ha₁₃ ha₂₃ hb₁₂ hb₁₃ hb₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃
      hf₁ hf₂ hf₃ hif₁ hif₂ hif₃ hPf₁ hPf₂ hPf₃ houtside
  obtain ⟨corrC, baseC, KC, goodC, hmod, hMPC, heligible, hcount, hlargeC,
    hgammaC, hbetaC⟩ :=
    Step1CaseTwoOutsidePrefixHierarchy G k e0 input T phi ett hMP hpositive
      hlower base H good hlarge hElementary beta gamma hbeta mu hgamma
      hproperMu honeMu hstable Bminus C hfixed hmissingFixed
      (by simpa [hlast] using hgammaMissing)
      (by simpa [hlast] using hbetaMissing) f₃
      (by simpa [hlast] using hif₃) hcolor hotherMissing
      hreserved hAB hBCstrict hCT
      hadjoin
  obtain ⟨J₁, J, corrJ, baseJ, KJ, goodJ, hMPCJ, hcountJ, hlargeJ,
    hgammaJ, hbetaJ, had₁, had₂, hf₁J, hf₂J, hb₁J, hb₂J, hb₃J⟩ :=
    Step1CaseTwoOutsideTwoEdgeExtension G k e0 input T phi mu ett hMP C
      corrC baseC KC goodC hmod hMPC heligible hlargeC beta gamma hgammaC
      hbetaC b₁ b₂ b₃ f₁ f₂ hbetaMissing hf₁mu hf₂mu hif₁ hif₂
      houtDistinct hb₁C hb₂C hb₃C
  exact ⟨gamma, mu, C, J₁, J, corrJ, baseJ, KJ, goodJ, R₁, R₂, R₃,
    hgamma, hproperMu, honeMu, hstable, hmod, hMPCJ,
    hcountJ.trans hcount, hlargeJ, hgammaJ, hbetaJ, hbetaMissing,
    hR₁, hR₂, hR₃, hd₁₂, hd₁₃, hd₂₃, hs₁, hs₂, hs₃, hl₁, hl₂, hl₃,
    hCT, hlast, had₁, had₂, hf₁J, hf₂J, hb₁J, hb₂J, hb₃J⟩

end GoldbergSeymour

end
