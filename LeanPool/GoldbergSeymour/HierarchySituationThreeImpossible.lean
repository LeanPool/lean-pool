/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationThreeComponentIntersectionShortening
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointPreparation
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointThetaStoredImpossible
public import
    LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointThetaUnstoredOutsideImpossible

/-!
# Hierarchy Situation Three Impossible

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchySituationThreeImpossible
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : forall (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu -> IsOneEdgeUncolored mu e0 ->
        forall v : V, (MissingColors G mu v).Nonempty) : False := by
  classical
  let I := HierarchyEligibleCommonMissingIndices
    G k e0 input T phi ett base C ctx
  have hclaim :
      exists P : HierarchyReplacementPresentation
          G k e0 input T phi ett base C ctx,
        exists alpha : Fin k,
          let H := P.counterexample.hierarchy
          let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
          let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
            Fin.last P.corresponding.replacementETT.rounds
          let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
          let B := HierarchyFullTailPrefix C
            (HierarchyPathNumber C.hierarchy - 2)
          let D := HierarchyStoredColorsAt H q
          let Gamma := D.biUnion (P.counterexample.good.gamma q)
          let baseExtraMissing :=
            ((TreeSequenceVertexSet P.replacementBase.core \
                TreeSequenceVertexSet Tn).biUnion
              fun v => MissingColors G P.coloring v)
          alpha ∈ MissingColors G P.coloring
              (T.vertex (Fin.last T.length)) ∧
            alpha ∈ TreeMissingColors P.coloring B ∧
            (alpha ∉ Gamma ∪ baseExtraMissing ∨
              exists eta : Fin k, eta ∈ D ∧
                alpha ∈ P.counterexample.good.gamma q eta ∧
                (HierarchyFirstMissingPosition P.coloring T eta).val <=
                  B.length) := by
    by_cases hI : I.Nonempty
    · exact HierarchySituationThreeClaimJMinusOneNonempty
        G k e0 input T phi ett base C ctx hpathLower hpathUpper
          hvertexMissing hI
    · exact HierarchySituationThreeClaimJMinusOneEmpty
        G k e0 input T phi ett base C ctx hpathLower hpathUpper
          hvertexMissing hI
  obtain ⟨P, alpha, halpha⟩ := hclaim
  obtain ⟨beta, hbeta⟩ := HierarchySituationThreeColorChoice
    G k e0 input T phi ett base C ctx P alpha hpathLower hpathUpper halpha
  let j := HierarchyPathNumber C.hierarchy
  let X := HierarchyFullTailPrefix C (j - 1)
  let Q := TwoColorComponent G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  by_cases hmeet : exists u, u ∈ TreeSequenceVertexSet X ∧ Sum.inl u ∈ Q
  · exact HierarchySituationThreeComponentIntersectionShortening
      G k e0 input T phi ett base C ctx P alpha beta hpathLower hpathUpper
        halpha hbeta hmeet
  · have hdisjoint : forall v, v ∈ TreeSequenceVertexSet X ->
        Sum.inl v ∉ Q := by
      intro v hv hmem
      exact hmeet ⟨v, hv, hmem⟩
    obtain ⟨d⟩ := HierarchySituationThreeDisjointPreparation
      G k e0 input T phi ett base C ctx P alpha beta hpathLower hpathUpper
        hvertexMissing halpha hbeta hdisjoint
    let H := d.switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    by_cases htheta : d.theta ∈ HierarchyStoredColorsAt H q
    · exact HierarchySituationThreeDisjointThetaStoredImpossible
        G k e0 input T phi ett base C ctx P alpha beta hpathLower hpathUpper
          hvertexMissing d htheta
    · rcases d.conditionNine with houtside | hstored
      · exact HierarchySituationThreeDisjointThetaUnstoredOutsideImpossible
          G k e0 input T phi ett base C ctx P alpha beta hpathLower
            hpathUpper hvertexMissing d htheta houtside
      · exact HierarchySituationThreeDisjointThetaUnstoredBetaStoredImpossible
          G k e0 input T phi ett base C ctx P alpha beta hpathLower
            hpathUpper hvertexMissing d htheta hstored

end GoldbergSeymour

end
