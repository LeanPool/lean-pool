/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesStep

/-!
# Simple Extension Seed Stored Color

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem SimpleExtensionSeedStoredColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (data : TashkinovSeriesData G k rounds e0)
    (j : Fin (rounds + 1))
    (hstep : TashkinovSeriesStep G k rounds e0 input data j)
    (hkind : data.kind j = some TashkinovExtensionKind.SE)
    (f : E) (hedges : data.connectingEdges j = {f})
    (beta : Fin k) (hcolor : data.coloring j f = some beta) :
    beta ∈ TashkinovStoredColors data j := by
  classical
  generalize hj : j = j' at hstep hkind hedges hcolor ⊢
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      rw [initialKind] at hkind
      simp at hkind
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hf : f = choice.edge := by
        have hm : f ∈ data.connectingEdges i.succ := by
          rw [hedges]
          simp
        rw [currentEdges] at hm
        simpa using hm
      subst f
      have hbeta : beta = choice.color := by
        rw [currentColoring] at hcolor
        exact Option.some.inj (hcolor.symm.trans choice.edgeColor)
      have hv : choice.vertex ∈
          TreeSequenceVertexSet (data.tree i.succ.castSucc) :=
        choice.vertexDefective.1
      have hpresentCurrent : choice.color ∈
          PresentColors G choice.selected choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨choice.edge, choice.edgeIncident, choice.edgeColor⟩
      have hnotCurrent : choice.color ∉
          MissingColors G choice.selected choice.vertex := by
        simp [MissingColors, hpresentCurrent]
      have hnotPrevious : choice.color ∉
          MissingColors G (data.coloring i.castSucc) choice.vertex := by
        rw [← choice.selectedStable.2 choice.vertex hv]
        exact hnotCurrent
      have hnotTreeCurrent : choice.color ∉
          TreeMissingColors choice.selected (data.tree i.succ.castSucc) := by
        intro hmissing
        simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing
        rcases hmissing with ⟨w, hw, hwmissing⟩
        have hwPrevious : choice.color ∈
            MissingColors G (data.coloring i.castSucc) w := by
          rw [← choice.selectedStable.2 w hw]
          exact hwmissing
        have hpresentPrevious : choice.color ∈
            PresentColors G (data.coloring i.castSucc) choice.vertex := by
          by_contra hpresent
          have : choice.color ∈
              MissingColors G (data.coloring i.castSucc) choice.vertex := by
            simp [MissingColors, hpresent]
          exact hnotPrevious this
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresentPrevious
        rcases hpresentPrevious with ⟨g, hgIncident, hgColor⟩
        have hgTree : TreeIncidentEdge (data.tree i.succ.castSucc) g :=
          ⟨choice.vertex, hv, hgIncident⟩
        have hgFixed : choice.selected g =
            data.coloring i.castSucc g := by
          apply choice.selectedStable.1 g hgTree
          refine ⟨choice.color, ?_, hgColor⟩
          simp only [Finset.mem_union]
          left
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨w, hw, hwPrevious⟩
        have hsame : g = choice.edge := by
          by_contra hne
          exact (choice.selectedProper hne
            ⟨choice.vertex, hgIncident, choice.edgeIncident⟩
            (hgFixed.trans hgColor)) choice.edgeColor
        subst g
        have hboundary : choice.edge ∈ BoundaryEdges G
            (TreeSequenceVertexSet (data.tree i.succ.castSucc)) := by
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨choice.vertex, hv, choice.otherEndpoint,
            choice.otherOutside, choice.edgeEnds⟩
        exact (previousClosed hboundary hw hgColor) hwPrevious
      have hnotTreeBeta : beta ∉ TreeMissingColors
          (data.coloring i.succ) (data.tree i.succ.castSucc) := by
        simpa [currentColoring, hbeta] using hnotTreeCurrent
      unfold TashkinovStoredColors
      simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte,
        Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨⟨i.succ, ?_⟩, hnotTreeBeta⟩
      simp [Fin.val_succ, currentStored, hbeta]
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      rw [currentKind] at hkind
      simp at hkind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      rw [currentKind] at hkind
      simp at hkind

end GoldbergSeymour

end
