/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePreservesTashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TashTree
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
    have vertexTransfer {X Y : TreeSequence G e0}
        (hab : TreeSequenceInitialSegment X Y) {v : V}
        (hv : v ∈ TreeSequenceVertexSet X) :
        v ∈ TreeSequenceVertexSet Y := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
      rcases hv with ⟨i, hi⟩
      rcases hab with ⟨hlen, hvertices, hedges⟩
      refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
      exact (hvertices i).trans hi
    have vertexReach {X Y : TreeSequence G e0}
        {phi : PartialEdgeColoring E k}
        (hab : TashkinovAugmentationSequence phi X Y) {v : V}
        (hv : v ∈ TreeSequenceVertexSet X) :
        v ∈ TreeSequenceVertexSet Y := by
      unfold TashkinovAugmentationSequence at hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl => exact hv
      | @head X Y hstep htail ih =>
          rcases hstep with ⟨hlen, hseg, hcolor⟩
          exact ih (vertexTransfer hseg hv)
    have incidentTransfer {X Y : TreeSequence G e0}
        (hab : TreeSequenceInitialSegment X Y) {f : E}
        (hf : TreeIncidentEdge X f) : TreeIncidentEdge Y f := by
      rcases hf with ⟨v, hv, hve⟩
      exact ⟨v, vertexTransfer hab hv, hve⟩
    have incidentReach {X Y : TreeSequence G e0}
        {phi : PartialEdgeColoring E k}
        (hab : TashkinovAugmentationSequence phi X Y) {f : E}
        (hf : TreeIncidentEdge X f) : TreeIncidentEdge Y f := by
      unfold TashkinovAugmentationSequence at hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl => exact hf
      | @head X Y hstep htail ih =>
          rcases hstep with ⟨hlen, hseg, hcolor⟩
          exact ih (incidentTransfer hseg hf)
    have closureReach {X Y : TreeSequence G e0}
        {phi : PartialEdgeColoring E k}
        (hab : TashkinovAugmentationSequence phi X Y) {v : V}
        (hv : v ∈ TreeSequenceVertexSet X) :
        v ∈ TreeSequenceVertexSet Y := vertexReach hab hv
    have sequenceSigma {X : TreeSequence G e0}
        (hreach : TashkinovAugmentationSequence
          (series.data.coloring 0) X (series.data.tree ⟨1, by omega⟩)) :
        TashkinovAugmentationSequence sigma X
          (series.data.tree ⟨1, by omega⟩) := by
      unfold TashkinovAugmentationSequence at hreach ⊢
      induction hreach using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head X Y hstep htail ih =>
          refine Relation.ReflTransGen.head ?_ ih
          rcases hstep with ⟨hlen, hseg, c, hcolor, hmissing⟩
          rcases hseg with ⟨hle, hvertices, hedges⟩
          let segment : TreeSequenceInitialSegment X Y :=
            ⟨hle, hvertices, hedges⟩
          refine ⟨hlen, segment, c, ?_, ?_⟩
          · rcases (show c ∈ TreeMissingColors (series.data.coloring 0) _
                from hmissing) with hcm
            rw [TreeMissingColors] at hcm
            rcases Finset.mem_biUnion.mp hcm with ⟨x, hx, hxc⟩
            have hx1 := closureReach htail
              (vertexTransfer segment hx)
            have hcm1 : c ∈ TreeMissingColors (series.data.coloring 0)
                (series.data.tree ⟨1, by omega⟩) := by
              rw [TreeMissingColors]
              exact Finset.mem_biUnion.mpr ⟨x, hx1, hxc⟩
            have hinc : TreeIncidentEdge
                (series.data.tree ⟨1, by omega⟩)
                (Y.edge (Fin.cast hlen.symm (Fin.last X.length))) := by
              let last : Fin Y.length :=
                Fin.cast hlen.symm (Fin.last X.length)
              obtain ⟨i, hi⟩ := Y.attaches last
              let q : Fin (X.length + 1) := ⟨i.val, by omega⟩
              let z : Fin (Y.length + 1) :=
                Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ last.isLt))
              have hz : Fin.castLE (Nat.succ_le_succ hle) q = z := by
                apply Fin.ext
                rfl
              have hzmem : Y.vertex z ∈ TreeSequenceVertexSet Y := by
                simp [TreeSequenceVertexSet]
              have hincY : TreeIncidentEdge Y
                  (Y.edge (Fin.cast hlen.symm (Fin.last X.length))) := by
                refine ⟨Y.vertex z, hzmem, ?_⟩
                unfold Incident
                change Y.vertex z ∈ G.ends (Y.edge last)
                rw [hi]
                exact Sym2.mem_mk_right _ _
              exact incidentReach htail hincY
            have heq := hstable.1 _ hinc
              (by exact ⟨c, Finset.mem_union_left _ hcm1, hcolor⟩)
            exact heq.trans hcolor
          · rw [TreeMissingColors] at hmissing
            rcases Finset.mem_biUnion.mp hmissing with ⟨x, hx, hxc⟩
            have hx1 := closureReach htail (vertexTransfer segment hx)
            rw [TreeMissingColors]
            exact Finset.mem_biUnion.mpr ⟨x, hx, by
              rw [hstable.2 x hx1]
              exact hxc⟩
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
