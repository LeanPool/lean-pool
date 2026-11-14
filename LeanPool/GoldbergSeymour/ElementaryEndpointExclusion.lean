/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# P2716_T2_Elementary Endpoint Exclusion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma P2716_T2_ElementaryEndpointExclusion {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T U : TreeSequence G e0)
    (alpha beta : Fin k) (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (ha₁₂ : a₁ ≠ a₂)
    (hb₁ : b₁ ∈ TreeSequenceVertexSet U)
    (hb₂ : b₂ ∈ TreeSequenceVertexSet U)
    (hb₃ : b₃ ∈ TreeSequenceVertexSet U)
    (helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet U))
    (hbeta : beta ∈ MissingColors G phi b₃)
    (hclosedBeta : TreeColorSetClosed G phi U {beta})
    (hclosedAlpha : alpha ∈ TreeMissingColors phi U →
      TreeColorSetClosed G phi U {alpha}) :
    a₁ ∉ TreeSequenceVertexSet U ∧ a₂ ∉ TreeSequenceVertexSet U ∧
      a₃ ∉ TreeSequenceVertexSet U := by
  classical
  let X := TreeSequenceVertexSet U
  have missing {a : V} (ha : a ∈ X) (hab : a ≠ b₃)
      (halt : alpha ∈ MissingColors G phi a ∨ beta ∈ MissingColors G phi a) :
      alpha ∈ MissingColors G phi a := by
    rcases halt with h | h
    · exact h
    · exact (Finset.disjoint_left.mp (helementary ha hb₃ hab) h hbeta).elim
  have outsideNe {a b : V}
      {P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl b)}
      (hP : TreeExitPath T phi alpha beta a b P) : a ≠ b₃ := by
    intro h
    exact hP.2.2.1 (h ▸ hP₃.2.2.2.1)
  have contain (halpha : alpha ∈ TreeMissingColors phi U) :
      ∀ {a b : V},
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl b) →
        b ∈ X → a ∈ X := by
    have haBoundary := hclosedAlpha halpha alpha (Finset.mem_singleton_self alpha)
    have hbBoundary := hclosedBeta beta (Finset.mem_singleton_self beta)
    let Inside : Sum V E → Prop
      | Sum.inl v => v ∈ X
      | Sum.inr e => ∀ v, Incident G v e → v ∈ X
    have step {z z' : Sum V E}
        (hzz' : (TwoColorIncidenceGraph G phi alpha beta).Adj z z')
        (hz : Inside z) : Inside z' := by
      cases z with
      | inl v =>
        cases z' with
        | inl w => exact hzz'.elim
        | inr e =>
          change Incident G v e ∧ (phi e = some alpha ∨ phi e = some beta) at hzz'
          intro w hw
          by_contra hwX
          have hvw : v ≠ w := by rintro rfl; exact hwX hz
          have hboundary : e ∈ BoundaryEdges G X := by
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨v, hz, w, hwX, (Sym2.mem_and_mem_iff hvw).mp ⟨hzz'.1, hw⟩⟩
          rcases hzz'.2 with hc | hc
          · have hm : e ∈ BoundaryColorEdges G phi X alpha :=
              Finset.mem_filter.mpr ⟨hboundary, hc⟩
            rw [haBoundary] at hm
            exact Finset.notMem_empty e hm
          · have hm : e ∈ BoundaryColorEdges G phi X beta :=
              Finset.mem_filter.mpr ⟨hboundary, hc⟩
            rw [hbBoundary] at hm
            exact Finset.notMem_empty e hm
      | inr e =>
        cases z' with
        | inl v => exact hz v hzz'.1
        | inr f => exact hzz'.elim
    intro a b P hb
    have hr := P.reverse.reachable
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    have hstay : ∀ z, Relation.ReflTransGen
        (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl b) z → Inside z := by
      intro z hz
      induction hz with
      | refl => exact hb
      | tail hreach hlast ih => exact step hlast ih
    exact hstay _ hr
  have impossible (halpha : alpha ∈ TreeMissingColors phi U) : False := by
    have ha₁ := contain halpha P₁ hb₁
    have ha₂ := contain halpha P₂ hb₂
    have hm₁ := missing ha₁ (outsideNe hP₁) hP₁.2.2.2.2.1
    have hm₂ := missing ha₂ (outsideNe hP₂) hP₂.2.2.2.2.1
    exact Finset.disjoint_left.mp (helementary ha₁ ha₂ ha₁₂) hm₁ hm₂
  have exclude {a b : V}
      {P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a) (Sum.inl b)}
      (hP : TreeExitPath T phi alpha beta a b P) : a ∉ X := by
    intro ha
    have hm := missing ha (outsideNe hP) hP.2.2.2.2.1
    exact impossible (Finset.mem_biUnion.mpr ⟨a, ha, hm⟩)
  exact ⟨exclude hP₁, exclude hP₂, exclude hP₃⟩

end GoldbergSeymour

end
