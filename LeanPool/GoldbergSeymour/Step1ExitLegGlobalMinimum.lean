/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Step1ExitLegMinimumExists
public import LeanPool.GoldbergSeymour.Step1ExitLegPrecoloringElementary
public import LeanPool.GoldbergSeymour.Step1ExitLegPresentationExists
public import LeanPool.GoldbergSeymour.Step1ExitLegThetaPositive
public import LeanPool.GoldbergSeymour.Step1ExitLegThetaZeroNonparallel
public import LeanPool.GoldbergSeymour.Step1ExitLegThetaZeroParallel
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Exit Leg Global Minimum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1ExitLegGlobalMinimum {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (_ : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < H.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (i : Fin H.dividerCount) (alpha beta : Fin k)
    (halpha : alpha ∈
      TreeMissingColors phi (H.stage i.succ.castSucc))
    (hne : alpha ≠ beta)
    (hclosed : TreeColorSetClosed G phi
      (H.stage i.succ.castSucc) {alpha})
    (hnot : ¬ TreeInterchangeable G
      (H.stage i.succ.castSucc) phi alpha beta) :
    ∃ (input' : PartialEdgeColoring E k) (T' : TreeSequence G e0)
      (psi : PartialEdgeColoring E k)
      (other : ExtendedTashkinovTree G k e0 input' T' psi)
      (base' : HierarchyBase other psi)
      (K : TashkinovHierarchy other base') (good' : GoodHierarchy K),
      other.rounds = ett.rounds ∧ MaximumProperty other ∧
      K.dividerCount < H.dividerCount ∧
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 ∧
      2 * other.rounds + 11 ≤
        (TreeMissingColors psi
          (other.series.data.tree (Fin.last other.rounds).castSucc)).card ∧
      TreeColorSetMinusClosed G psi T'
        ((HierarchyTerminalStoredColors K).biUnion
          (good'.gamma (Fin.last K.dividerCount))) ∧
      ColoredVertexSetElementary G psi (TreeSequenceVertexSet T') ∧
      ∃ (a b theta : Fin k)
        (a₁ b₁ a₂ b₂ : V)
        (P₁ : (TwoColorIncidenceGraph G psi a b).Walk
          (Sum.inl a₁) (Sum.inl b₁))
        (P₂ : (TwoColorIncidenceGraph G psi a b).Walk
          (Sum.inl a₂) (Sum.inl b₂))
        (f₁ f₂ : E),
        a ≠ b ∧ a ∈ TreeMissingColors psi T' ∧
        TreeColorSetClosed G psi T' {a} ∧
        TreeExitPath T' psi a b a₁ b₁ P₁ ∧
        TreeExitPath T' psi a b a₂ b₂ P₂ ∧
        (∀ x, x ∈ P₁.support → x ∉ P₂.support) ∧
        a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ TreeVertexOrder T' b₁ b₂ ∧
        f₁ ∈ BoundaryColorEdges G psi (TreeSequenceVertexSet T') b ∧
        f₂ ∈ BoundaryColorEdges G psi (TreeSequenceVertexSet T') b ∧
        Incident G b₁ f₁ ∧ Incident G b₂ f₂ ∧
        Sum.inr f₁ ∈ P₁.support ∧ Sum.inr f₂ ∈ P₂.support ∧
        theta ≠ a ∧ theta ≠ b ∧
        theta ∈ TreeMissingColors psi
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        TreeColorSetClosed G psi
          (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta} ∧
        TreeColorSetClosed G psi T' {theta} ∧
        (∀ (sigma : PartialEdgeColoring E k) (U : TreeSequence G e0)
          (corr : CorrespondingExtendedTashkinovTree G k e0 other sigma U),
          IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
          StableColoring
            (other.series.data.tree (Fin.last other.rounds).castSucc)
            (TashkinovStoredColors other.series.data
              (Fin.last other.rounds)) psi sigma →
          MaximumProperty corr.replacementETT →
          ∀ (baseU : HierarchyBase corr.replacementETT sigma)
            (L : TashkinovHierarchy corr.replacementETT baseU)
            (goodU : GoodHierarchy L),
            L.dividerCount < K.dividerCount →
            2 * corr.replacementETT.rounds + 11 ≤
              (TreeMissingColors sigma
                (corr.replacementETT.series.data.tree
                  (Fin.last corr.replacementETT.rounds).castSucc)).card →
            TreeColorSetMinusClosed G sigma U
              ((HierarchyTerminalStoredColors L).biUnion
                (goodU.gamma (Fin.last L.dividerCount))) →
            ∀ (c d : Fin k), c ≠ d →
              c ∈ TreeMissingColors sigma U →
              TreeColorSetClosed G sigma U {c} →
              ∀ (u₁ v₁ u₂ v₂ : V)
                (Q₁ : (TwoColorIncidenceGraph G sigma c d).Walk
                  (Sum.inl u₁) (Sum.inl v₁))
                (Q₂ : (TwoColorIncidenceGraph G sigma c d).Walk
                  (Sum.inl u₂) (Sum.inl v₂)),
                TreeExitPath U sigma c d u₁ v₁ Q₁ →
                TreeExitPath U sigma c d u₂ v₂ Q₂ →
                (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
                u₁ ≠ u₂ → False) ∧
        (b ∈ TreeMissingColors psi T' ∨
          (b ∉ TreeMissingColors psi T' ∧
            ∃ (a₃ b₃ : V)
              (P₃ : (TwoColorIncidenceGraph G psi a b).Walk
                (Sum.inl a₃) (Sum.inl b₃)) (f₃ : E),
              TreeExitPath T' psi a b a₃ b₃ P₃ ∧
              (∀ x, x ∈ P₁.support → x ∉ P₃.support) ∧
              (∀ x, x ∈ P₂.support → x ∉ P₃.support) ∧
              a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
              b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧
              TreeVertexOrder T' b₂ b₃ ∧
              f₃ ∈ BoundaryColorEdges G psi
                (TreeSequenceVertexSet T') b ∧
              Incident G b₃ f₃ ∧ Sum.inr f₃ ∈ P₃.support ∧
              (∀ (sigma : PartialEdgeColoring E k)
                (U : TreeSequence G e0)
                (corr : CorrespondingExtendedTashkinovTree
                  G k e0 other sigma U),
                IsProperEdgeColoring G sigma →
                IsOneEdgeUncolored sigma e0 →
                StableColoring
                  (other.series.data.tree
                    (Fin.last other.rounds).castSucc)
                  (TashkinovStoredColors other.series.data
                    (Fin.last other.rounds)) psi sigma →
                MaximumProperty corr.replacementETT →
                ∀ (baseU : HierarchyBase corr.replacementETT sigma)
                  (L : TashkinovHierarchy corr.replacementETT baseU)
                  (goodU : GoodHierarchy L),
                  L.dividerCount = K.dividerCount →
                  2 * corr.replacementETT.rounds + 11 ≤
                    (TreeMissingColors sigma
                      (corr.replacementETT.series.data.tree
                        (Fin.last corr.replacementETT.rounds).castSucc)).card →
                  TreeColorSetMinusClosed G sigma U
                    ((HierarchyTerminalStoredColors L).biUnion
                      (goodU.gamma (Fin.last L.dividerCount))) →
                  ∀ (c d : Fin k), c ≠ d →
                    c ∈ TreeMissingColors sigma U →
                    TreeColorSetClosed G sigma U {c} →
                    ∀ (u₁ v₁ u₂ v₂ : V)
                      (Q₁ : (TwoColorIncidenceGraph G sigma c d).Walk
                        (Sum.inl u₁) (Sum.inl v₁))
                      (Q₂ : (TwoColorIncidenceGraph G sigma c d).Walk
                        (Sum.inl u₂) (Sum.inl v₂)),
                      TreeExitPath U sigma c d u₁ v₁ Q₁ →
                      TreeExitPath U sigma c d u₂ v₂ Q₂ →
                      (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
                      u₁ ≠ u₂ →
                      (d ∈ TreeMissingColors sigma U ∨
                        (d ∉ TreeMissingColors sigma U ∧
                          ∃ (u₃ v₃ : V)
                            (Q₃ : (TwoColorIncidenceGraph G sigma c d).Walk
                              (Sum.inl u₃) (Sum.inl v₃)),
                            TreeExitPath U sigma c d u₃ v₃ Q₃ ∧
                            (∀ x, x ∈ Q₁.support → x ∉ Q₃.support) ∧
                            (∀ x, x ∈ Q₂.support → x ∉ Q₃.support) ∧
                            u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
                            Q₁.length + Q₂.length + Q₃.length <
                              P₁.length + P₂.length + P₃.length)) →
                      False))) := by
  have hfamily : Nonempty
      (Step1ExitLegPresentation G k e0 ett.rounds H.dividerCount) :=
    Step1ExitLegPresentationExists G k e0 input T phi ett hMP hproper hone
      base H good hfewer hlarge i alpha beta halpha hne hclosed hnot
  have hallElementary : ∀ P :
      Step1ExitLegPresentation G k e0 ett.rounds H.dividerCount,
      ColoredVertexSetElementary G P.phi (TreeSequenceVertexSet P.T) := by
    intro P
    exact hfewer P.ett P.rounds_eq P.maximum P.base P.hierarchy P.good
      P.divider_lt
  obtain ⟨M⟩ := Step1ExitLegMinimumExists G k e0 ett.rounds
    H.dividerCount hfamily hallElementary
  have hlowerElementary :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), 0 < lower.rounds → lower.rounds < M.selected.ett.rounds → MaximumProperty
        lower → ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T') := by
    intro input' T' generating' lower hlowerPositive hlowerRounds hlowerMP
    have hlowerRounds' : lower.rounds < ett.rounds := by
      simpa only [M.selected.rounds_eq] using hlowerRounds
    have hpack := hlower lower hlowerPositive hlowerRounds' hlowerMP
    intro u hu v hv huv
    exact hpack.1 hu hv huv
  have htheta : ∃ theta : Fin k,
      theta ≠ M.selected.a ∧ theta ≠ M.selected.b ∧
      theta ∈ TreeMissingColors M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) ∧
      TreeColorSetClosed G M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) {theta} ∧
      TreeColorSetClosed G M.selected.phi M.selected.T {theta} := by
    by_cases hzero : M.selected.hierarchy.dividerCount = 0
    · by_cases hparallel :
          M.selected.ett.series.data.kind
              (Fin.last M.selected.ett.rounds) =
            some TashkinovExtensionKind.PE
      · exact Step1ExitLegThetaZeroParallel G k e0 ett.rounds
          H.dividerCount M.selected hzero hparallel
          (Step1ExitLegPrecoloringElementary G k e0 ett.rounds
            H.dividerCount M.selected hlowerElementary)
      · exact Step1ExitLegThetaZeroNonparallel G k e0 ett.rounds
          H.dividerCount M.selected hzero hparallel
    · exact Step1ExitLegThetaPositive G k e0 ett.rounds H.dividerCount M
        (Nat.pos_of_ne_zero hzero)
  obtain ⟨theta, hthetaA, hthetaB, hthetaMissing, hthetaStarClosed,
    hthetaTerminalClosed⟩ := htheta
  refine ⟨M.selected.input, M.selected.T, M.selected.phi, M.selected.ett,
    M.selected.base, M.selected.hierarchy, M.selected.good,
    M.selected.rounds_eq, M.selected.maximum, M.selected.divider_lt,
    M.selected.proper, M.selected.oneUncolored, M.selected.large,
    M.selected.terminalMinusClosed, M.elementary, M.selected.a,
    M.selected.b, theta, M.selected.a1, M.selected.b1, M.selected.a2,
    M.selected.b2, M.selected.P1, M.selected.P2, M.selected.f1,
    M.selected.f2, M.selected.a_ne_b, M.selected.aMissing,
    M.selected.aClosed, M.selected.exit1, M.selected.exit2,
    M.selected.disjoint12, M.selected.outsideDistinct,
    M.selected.treeDistinct, M.selected.treeOrder, M.selected.boundary1,
    M.selected.boundary2, M.selected.incident1, M.selected.incident2,
    M.selected.support1, M.selected.support2, hthetaA, hthetaB,
    hthetaMissing, hthetaStarClosed, hthetaTerminalClosed,
    M.primaryMinimal, M.secondary⟩

end GoldbergSeymour

end
