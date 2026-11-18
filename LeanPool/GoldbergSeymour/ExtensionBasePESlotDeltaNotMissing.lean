/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# Extension Base PESlot Delta Not Missing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBasePESlotDeltaNotMissing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (r : Fin rounds) (delta : Fin k)
    (hkind : series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hdelta : series.data.delta r.succ = some delta) :
    delta ∉ TreeMissingColors (series.data.coloring r.castSucc)
      (series.data.tree r.succ.castSucc) := by
  classical
  have step := series.certified r.succ
  generalize hz : r.succ = z at step
  cases step with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hv := congrArg Fin.val hz
      simp at hv
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hir : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst i
      rw [currentKind] at hkind
      simp at hkind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hir : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst i
      rw [currentKind] at hkind
      simp at hkind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hir : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hz
        simp at hv ⊢
        omega
      subst i
      have hcolor : choice.color = delta := by
        rw [currentDelta] at hdelta
        exact Option.some.inj hdelta
      subst delta
      intro hmissing
      simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing
      obtain ⟨v, hv, hvmissing⟩ := hmissing
      have hselectedMissing : choice.color ∈ MissingColors G choice.selected v := by
        rw [choice.selectedStable.2 v hv]
        exact hvmissing
      have hedgeIncident : TreeIncidentEdge
          (series.data.tree r.succ.castSucc) choice.edge :=
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      have hrefColor : series.data.coloring r.castSucc choice.edge =
          some choice.color := by
        have hcontrolled : choice.color ∈
            TreeMissingColors (series.data.coloring r.castSucc)
                (series.data.tree r.succ.castSucc) ∪
              TashkinovStoredColors series.data r.castSucc :=
          Finset.mem_union_left _ (by
            simp only [TreeMissingColors, Finset.mem_biUnion]
            exact ⟨v, hv, hvmissing⟩)
        have hfixed := (sc1 G e0 (series.data.tree r.succ.castSucc)
          (TashkinovStoredColors series.data r.castSucc)
          (series.data.coloring r.castSucc) choice.selected
          previousProper previousOneUncolored choice.selectedProper
          choice.selectedOneUncolored).mp choice.selectedStable choice.edge
            hedgeIncident (Or.inr ⟨choice.color, hcontrolled,
              choice.edgeColor⟩)
        exact hfixed.symm.trans choice.edgeColor
      obtain ⟨alpha, hdefective, hedgeColor⟩ := choice.edgeDefective
      have hedgeBoundary : choice.edge ∈ BoundaryEdges G
          (TreeSequenceVertexSet (series.data.tree r.succ.castSucc)) := by
        exact (Finset.mem_filter.mp hedgeColor).1
      exact previousClosed hedgeBoundary hv hrefColor hvmissing

end GoldbergSeymour

end
