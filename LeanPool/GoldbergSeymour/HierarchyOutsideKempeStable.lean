/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.CombinedStableColoring

public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable

public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Hierarchy Outside Kempe Stable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyOutsideKempeStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    StableColoring T Dn phi sigma ∧ TreeColoringInvariant T phi sigma ∧
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
      CombinedStableColoring Tn base.closure Dn phi sigma) := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  dsimp [n, Tn, Dn]
  have stable := OutsideKempeRecoloringStable G e0 T
    (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    phi sigma alpha beta hproper hone hrecolor
  refine ⟨stable.1, stable.2.1, stable.2.2.1, stable.2.2.2.1, ?_⟩
  intro hkind
  unfold CombinedStableColoring
  have coreToT : TreeSequenceInitialSegment base.core T := by
    exact (H.coreInitialSegmentOfStarredStage (Fin.last _)).trans
      H.lastStarredInitialSegment
  rcases base.parallel hkind with ⟨chosen, closed, unionExists⟩
  obtain ⟨unionCert⟩ := unionExists
  have unionToT : TreeSequenceInitialSegment base.core T := coreToT
  have vertexCore : TreeSequenceVertexSet base.core ⊆ TreeSequenceVertexSet T := by
    exact unionToT.vertexSet_subset
  have unionVertex : TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∪
      TreeSequenceVertexSet base.closure = TreeSequenceVertexSet base.core := by
    exact unionCert.vertexSet.symm
  have treeSubset : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet T := by
    intro v hv
    have hvc : v ∈ TreeSequenceVertexSet base.core := by
      rw [← unionVertex]
      exact (Finset.mem_union_left _ hv)
    exact vertexCore hvc
  have closureSubset : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet T := by
    intro v hv
    have hvc : v ∈ TreeSequenceVertexSet base.core := by
      rw [← unionVertex]
      exact (Finset.mem_union_right _ hv)
    exact vertexCore hvc
  have fixedTree : ∀ f, TreeIncidentEdge Tn f → sigma f = phi f := by
    intro f hf
    rcases hf with ⟨v, hv, hinc⟩
    apply stable.2.2.2.2 f
    exact ⟨v, treeSubset hv, hinc⟩
  have fixedClosure : ∀ f, TreeIncidentEdge base.closure f → sigma f = phi f := by
    intro f hf
    rcases hf with ⟨v, hv, hinc⟩
    apply stable.2.2.2.2 f
    exact ⟨v, closureSubset hv, hinc⟩
  constructor
  · unfold StableColoring
    constructor
    · intro f hf hcol
      exact fixedTree f hf
    · intro v hv
      exact (stable.2.2.1).2 v (treeSubset hv)
  · unfold StableColoring
    constructor
    · intro f hf hcol
      exact fixedClosure f hf
    · intro v hv
      exact (stable.2.2.1).2 v (closureSubset hv)

end GoldbergSeymour

end
