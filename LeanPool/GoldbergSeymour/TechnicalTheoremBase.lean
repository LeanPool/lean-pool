/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.Tchange
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# Technical Theorem Base

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TechnicalTheoremBase {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) :
    ColoredVertexSetElementary G (series.data.coloring 0)
        (TreeSequenceVertexSet (series.data.tree ⟨1, by omega⟩)) ∧
      (let i0 : Fin (rounds + 1) := 0
      let T1 : TreeSequence G e0 := series.data.tree ⟨1, by omega⟩
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma →
          IsOneEdgeUncolored sigma e0 →
            StableColoring T1 (TashkinovStoredColors series.data i0)
                (series.data.coloring i0) sigma →
              ∀ alpha beta : Fin k,
                (alpha ∈ TreeMissingColors sigma T1 ∨ beta ∈ TreeMissingColors sigma T1) →
                  TreeInterchangeable G T1 sigma alpha beta) := by
  classical
  have initial := series.certified (0 : Fin (rounds + 1))
  cases initial with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have seedTree : TashkinovTree G e0 (series.data.coloring 0)
        (series.data.tree 0) := by
      intro j hj
      rw [seedLength] at j
      omega
    have triple' : KTriple G k e0 (series.data.coloring 0) := by
      simpa [initialColoring] using triple
    have treeOne : TashkinovTree G e0 (series.data.coloring 0)
        (series.data.tree ⟨1, by omega⟩) :=
      TashkinovAugmentationSequencePreservesTashkinovTree G e0
        (series.data.coloring 0) (series.data.tree 0)
        (series.data.tree ⟨1, by omega⟩) seedTree initialClosure.1
    have elementary : ColoredVertexSetElementary G (series.data.coloring 0)
        (TreeSequenceVertexSet (series.data.tree ⟨1, by omega⟩)) :=
      TashTree G k e0 (series.data.coloring 0)
      (series.data.tree ⟨1, by omega⟩) triple' treeOne
    refine ⟨elementary, ?_⟩
    dsimp
    intro sigma hproper hone hstable alpha beta hmissing
    have sequenceSigma {X : TreeSequence G e0}
        (route : TashkinovAugmentationSequence
          (series.data.coloring 0) X (series.data.tree ⟨1, by omega⟩)) :
        TashkinovAugmentationSequence sigma X (series.data.tree ⟨1, by omega⟩) :=
      TashkinovAugmentationSequence.transport_of_stable hstable route
    have sigmaReach := sequenceSigma initialClosure.1
    exact (Tchange G k e0 sigma (series.data.tree ⟨1, by omega⟩)
    ⟨triple'.1, triple'.2.1, triple'.2.2.1, hproper, hone⟩
    (TashkinovAugmentationSequencePreservesTashkinovTree G e0 sigma
      (series.data.tree 0) (series.data.tree ⟨1, by omega⟩)
      (by intro j hj; omega) sigmaReach)
    (by
      unfold ColoredVertexSetClosed
      intro f c v hf hv hfc hcv
      have hmissingSigma : c ∈ TreeMissingColors sigma
          (series.data.tree ⟨1, by omega⟩) := by
        rw [TreeMissingColors]
        exact Finset.mem_biUnion.mpr ⟨v, hv, hcv⟩
      have hmissingPhi : c ∈ TreeMissingColors
          (series.data.coloring 0)
          (series.data.tree ⟨1, by omega⟩) := by
        rw [TreeMissingColors]
        rcases Finset.mem_biUnion.mp hmissingSigma with ⟨x, hx, hcx⟩
        exact Finset.mem_biUnion.mpr ⟨x, hx, by
          rw [← hstable.2 x hx]
          exact hcx⟩
      have boundary := hf
      have hinc : TreeIncidentEdge
          (series.data.tree ⟨1, by omega⟩) f := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨u, hu, w, hw, he⟩
        exact ⟨u, hu, by
          unfold Incident
          rw [he]
          exact Sym2.mem_mk_left _ _⟩
      have hreverse := (sc1 G e0 (series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors series.data 0)
        (series.data.coloring 0) sigma triple'.2.2.2.1 triple'.2.2.2.2
        hproper hone).mp hstable
      have heq := hreverse f hinc
        (Or.inr ⟨c, Finset.mem_union_left _ hmissingPhi, hfc⟩)
      have hphi : (series.data.coloring 0) f = some c := by
        rw [← heq]
        exact hfc
      rw [hstable.2 v hv] at hcv
      exact (initialClosure.2 boundary hv hphi) hcv)
    alpha beta hmissing)

end GoldbergSeymour

end
