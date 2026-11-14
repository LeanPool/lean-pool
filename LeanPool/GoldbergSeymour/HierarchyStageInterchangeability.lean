/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Step1CaseOneInsideStar
public import LeanPool.GoldbergSeymour.Step1CaseOneOutsideStar
public import LeanPool.GoldbergSeymour.Step1CaseTwoInsideStar
public import LeanPool.GoldbergSeymour.Step1CaseTwoOutsideStar

public import LeanPool.GoldbergSeymour.Step1ExitLegGlobalMinimum

/-!
# step1

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem step1 {V E : Type*}
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
      (H.stage i.succ.castSucc) {alpha}) :
    TreeInterchangeable G (H.stage i.succ.castSucc) phi alpha beta := by
  by_contra hnot
  obtain ⟨input', T', psi, other, base', K, good', hround, hmp', hdiv,
    hproper', hone', hlarge', hterm', helem', hrest⟩ :=
    Step1ExitLegGlobalMinimum G k e0 input T phi ett hMP hpositive hproper hone
      hlower base H good hfewer hlarge i alpha beta halpha hne hclosed hnot
  rcases hrest with ⟨a, b, theta, a₁, b₁, a₂, b₂, P₁, P₂, f₁, f₂,
    hab, ha, hac, hp₁, hp₂, hpaths, haa, hbb, horder, hf₁, hf₂,
    hi₁, hi₂, hpf₁, hpf₂, hta, htb, htm, htcstar, htc, hnoSmaller,
    hcases⟩
  have hpos : 0 < other.rounds := by omega
  rcases hcases with hmissing | ⟨hnotmissing, hthird⟩
  · by_cases hinside : b₂ ∈ TreeSequenceVertexSet
      (HierarchyStarredStage K (Fin.last K.dividerCount))
    · exact Step1CaseOneInsideStar G k e0 input' T' psi other hmp' hpos
        hproper' hone' (fun lower hp hlt hm => hlower lower hp (by omega) hm)
        base' K good' H.dividerCount hdiv
        (fun lower hr hm => hfewer lower (by omega) hm) hlarge' hterm' helem'
        a b ha hac hab hmissing a₁ b₁ a₂ b₂ P₁ P₂ hp₁ hp₂ hpaths haa hbb horder
        f₁ f₂ hf₁ hf₂ hi₁ hi₂ hpf₁ hpf₂ hinside theta hta htb htm htcstar htc
        hnoSmaller
    · exact Step1CaseOneOutsideStar G k e0 input' T' psi other hmp' hpos
        hproper' hone' (fun lower hp hlt hm => hlower lower hp (by omega) hm)
        base' K good' H.dividerCount hdiv
        (fun lower hr hm => hfewer lower (by omega) hm) hlarge' hterm' helem'
        a b ha hac hab hmissing a₁ b₁ a₂ b₂ P₁ P₂ hp₁ hp₂ hpaths haa hbb horder
        f₁ f₂ hf₁ hf₂ hi₁ hi₂ hpf₁ hpf₂ hinside
  · rcases hthird with ⟨a₃, b₃, P₃, f₃, hp₃, hpaths₁₃, hpaths₂₃,
      haa₃, haa₃', hbb₃, hbb₃', horder₃, hf₃, hi₃, hpf₃, hnoBetter⟩
    by_cases hinside : b₃ ∈ TreeSequenceVertexSet
        (HierarchyStarredStage K (Fin.last K.dividerCount))
    · exact Step1CaseTwoInsideStar G k e0 input' T' psi other hmp' hpos
        hproper' hone' (fun lower hp hlt hm => hlower lower hp (by omega) hm)
        base' K good' H.dividerCount hdiv
        (fun lower hr hm => hfewer lower (by omega) hm) hlarge' hterm' helem'
        a b ha hac hab hnotmissing a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃ hp₁ hp₂ hp₃
        hpaths hpaths₁₃ hpaths₂₃ haa haa₃ haa₃' hbb hbb₃ hbb₃' horder horder₃
        f₁ f₂ f₃ hf₁ hf₂ hf₃ hi₁ hi₂ hi₃ hpf₁ hpf₂ hpf₃ hinside theta hta htb
        htm htcstar htc hnoSmaller
    · exact Step1CaseTwoOutsideStar G k e0 input' T' psi other hmp' hpos
        hproper' hone' (fun lower hp hlt hm => hlower lower hp (by omega) hm)
        base' K good' H.dividerCount hdiv
        (fun lower hr hm => hfewer lower (by omega) hm) hlarge' hterm' helem'
        a b ha hac hab hnotmissing a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃ hp₁ hp₂ hp₃
        hpaths hpaths₁₃ hpaths₂₃ haa haa₃ haa₃' hbb hbb₃ hbb₃' horder horder₃
        f₁ f₂ f₃ hf₁ hf₂ hf₃ hi₁ hi₂ hi₃ hpf₁ hpf₂ hpf₃ hinside hnoBetter

end GoldbergSeymour

end
