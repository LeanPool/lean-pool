/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTrans
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Preparatory lemmas for hierarchy normalization

Extracted from Wesley Pegden’s Trellis formalization of the Goldberg–Seymour
theorem at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish
properties used in the computed hierarchy records of `HierarchyClaimNinePENormalization`.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchyNormalizationLemmas

theorem helper_branch_909.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let F : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let b : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let X : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := X.hierarchy;
    let n : Fin (F.rounds + (1 : ℕ)) := Fin.last F.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let y : V := T.vertex (Fin.last T.length); F.series.data.kind n = some
        TashkinovExtensionKind.PE → A = b.core → alpha ∈ TreeMissingColors mu A →
    let D : Finset (Fin k) := HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)));
    let R : Finset (Fin k) := D.biUnion (X.good.gamma (0 : Fin (X.hierarchy.dividerCount + (1 :
        ℕ))));
    ∀ beta ∉ R, alpha ∉ R → beta ∈ TreeMissingColors mu A →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu beta alpha (Sum.inl y);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 F sigma T) (bs : HierarchyBase
        corr.replacementETT sigma) (K : TashkinovHierarchy corr.replacementETT bs), bs.core = A →
        (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), HierarchyStarredStage K j = bs.core) → (
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))), K.stage j.succ = T) → H.stage (Fin.succ (0 : Fin
        (H.dividerCount + (1 : ℕ)))) = T → (
    ∀ (f : E) (c : Fin k), c ≠ beta → c ≠ alpha → (sigma f = some c ↔ mu f = some c)) → (
    ∀ (eta : Fin k), eta ≠ beta → eta ≠ alpha → HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta) →
    ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt K j,
    ∀ ⦃c : Fin k⦄, c ∈ X.good.gamma (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ))) eta → eta ∈ D →
        c ∈ HierarchyStageMissingColors X.hierarchy (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ)))
        \ HierarchySegmentColors X.hierarchy (0 : Fin (X.hierarchy.dividerCount + (1 : ℕ))) eta →
        c ∉ HierarchySegmentColors K j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu F b X H n A y hp hA haA D R beta
      hbR haRnot hbA sigma corr bs K coreEq starK termK termH unaffectedValue firstEq j eta heta
      c hcg hetaD hold hseg
  have hn : eta ∉ TreeMissingColors mu A := by
    have hn := (Finset.mem_sdiff.mp hetaD).2
    change eta ∉ TreeMissingColors mu b.core at hn
    rwa [← hA] at hn
  have heb : eta ≠ beta := by intro h; subst eta; exact hn hbA
  have hea : eta ≠ alpha := by intro h; subst eta; exact hn haA
  have hcR : c ∈ R := Finset.mem_biUnion.mpr ⟨eta, hetaD, hcg⟩
  have hcb : c ≠ beta := by intro h; subst c; exact hbR hcR
  have hca : c ≠ alpha := by intro h; subst c; exact haRnot hcR
  have hfirst := firstEq eta heb hea
  change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (K.stage j.succ).length,
    (HierarchyStarredStage K j).length ≤ r.val ∧
      r.val < min (HierarchyFirstMissingPosition sigma T eta).val (K.stage j.succ).length ∧
      sigma ((K.stage j.succ).edge r) = some c) at hseg
  rw [starK j, coreEq, termK j, hfirst] at hseg
  obtain ⟨r, hr, hp, hcol⟩ := (Finset.mem_filter.mp hseg).2
  apply (Finset.mem_sdiff.mp hold).2
  change c ∈ Finset.univ.filter (fun c => ∃ r : Fin (H.stage (0 : Fin (H.dividerCount +
      1)).succ).length,
    b.core.length ≤ r.val ∧
      r.val < min (HierarchyFirstMissingPosition mu T eta).val (H.stage (0 : Fin (H.dividerCount
          + 1)).succ).length ∧
      mu ((H.stage (0 : Fin (H.dividerCount + 1)).succ).edge r) = some c)
  rw [termH, ← hA]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hr, hp, (unaffectedValue _ c hcb hca).1 hcol⟩

end GoldbergSeymour.HierarchyNormalizationLemmas

end
