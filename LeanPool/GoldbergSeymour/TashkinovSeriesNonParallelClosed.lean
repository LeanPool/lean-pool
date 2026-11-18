/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# Closure of nonparallel series stages

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Stable proper colorings preserve closure of a tree's vertex set. -/
theorem StableColoring.closed {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (B : TreeSequence G e0) (D : Finset (Fin k)) (psi phi : PartialEdgeColoring E k)
    (hppsi : IsProperEdgeColoring G psi) (hopsi : IsOneEdgeUncolored psi e0)
    (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0)
    (hcpsi : ColoredVertexSetClosed G psi (TreeSequenceVertexSet B))
    (hs : StableColoring B D psi phi) :
    ColoredVertexSetClosed G phi (TreeSequenceVertexSet B) := by
  classical
  intro f c x hf hx hfc hcm
  have hincident : TreeIncidentEdge B f := by
    obtain ⟨u, hu, v, hv, huv⟩ := by
      simpa [BoundaryEdges] using hf
    refine ⟨u, hu, ?_⟩
    change u ∈ G.ends f
    rw [huv]
    exact Sym2.mem_mk_left _ _
  have hcmPrev : c ∈ MissingColors G psi x := by
    rw [← hs.2 x hx]
    exact hcm
  have hcTree : c ∈ TreeMissingColors psi B :=
    Finset.mem_biUnion.mpr ⟨x, hx, hcmPrev⟩
  have hfixed : phi f = psi f :=
    (sc1 G e0 B D psi phi hppsi hopsi hproper hone).mp hs
      f hincident (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hfc⟩)
  exact hcpsi hf hx (hfixed.symm.trans hfc) hcmPrev

/-- A positive nonparallel series stage is closed under its current proper coloring. -/
theorem TashkinovSeries.closedOfNonParallel {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (n : Fin (rounds + 1)) (hp : 0 < n.val) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0)
    (hphi : phi = series.data.coloring n)
    (hnonPE : series.data.kind n ≠ some TashkinovExtensionKind.PE) :
    ColoredVertexSetClosed G phi (TreeSequenceVertexSet (series.data.tree n.castSucc)) := by
  classical
  have hn : n ≠ 0 := by
    intro equal
    have zero : n.val = 0 := congrArg Fin.val equal
    omega
  generalize hTn : series.data.tree n.castSucc = Tn
  have hstep := series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      exact (hn targetEq).elim
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      exact (hnonPE (by rw [targetEq]; exact currentKind)).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i.succ = n := targetEq.symm
      have htree : series.data.tree i.succ.castSucc = Tn := by
        rw [hi]
        exact hTn
      have hselected : choice.selected = phi :=
        currentColoring.symm.trans
          ((congrArg series.data.coloring hi).trans hphi.symm)
      have hs : StableColoring Tn
          (TashkinovStoredColors series.data i.castSucc)
          (series.data.coloring i.castSucc) phi := by
        simpa only [htree, hselected] using choice.selectedStable
      exact @StableColoring.closed _ _ _ _ G k e0 Tn _ _ phi previousProper previousOneUncolored
        hproper hone (by rw [← htree]; exact previousClosed) hs
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i.succ = n := targetEq.symm
      have htree : series.data.tree i.succ.castSucc = Tn := by
        rw [hi]
        exact hTn
      have hcol : series.data.coloring i.castSucc = phi :=
        currentColoring.symm.trans
          ((congrArg series.data.coloring hi).trans hphi.symm)
      have hc : ColoredVertexSetClosed G (series.data.coloring i.castSucc)
          (TreeSequenceVertexSet Tn) := by
        rw [← htree]
        exact previousClosed
      exact @Eq.mp _ _
        (congrArg (fun psi => ColoredVertexSetClosed G psi
          (TreeSequenceVertexSet Tn)) hcol) (@hc)

end GoldbergSeymour

end
