/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion

/-!
# P2647_T1_Terminal Stable Route

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem P2647_T1_TerminalStableRoute
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (original.series.data.tree (Fin.last (original.rounds + 1)))
      (TashkinovStoredColors original.series.data (Fin.last original.rounds))
      (original.series.data.coloring (Fin.last original.rounds)) sigma) :
    let n := Fin.last original.rounds
    let Tn := original.series.data.tree n.castSucc
    let F := original.series.data.tree (Fin.last (original.rounds + 1))
    let phi := original.series.data.coloring n
    let D := TashkinovStoredColors original.series.data n
    IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
      TreeSequenceInitialSegment Tn F ∧ Tn.length < F.length ∧
      StableColoring Tn D phi sigma ∧
      ((original.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovClosure sigma Tn F) ∨
        ((original.series.data.kind n = some TashkinovExtensionKind.SE ∨
            original.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            original.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovClosure sigma seed F)) := by
  classical
  let n := Fin.last original.rounds
  let Tn := original.series.data.tree n.castSucc
  let F := original.series.data.tree (Fin.last (original.rounds + 1))
  let phi := original.series.data.coloring n
  let D := TashkinovStoredColors original.series.data n
  let q : Fin original.rounds := ⟨original.rounds - 1, by
    have := original.roundsPositive
    omega⟩
  have hq : q.succ = n := by
    apply Fin.ext
    dsimp [q, n]
    have := original.roundsPositive
    omega
  have hnFinal : n.succ = Fin.last (original.rounds + 1) := rfl
  have transport {S : TreeSequence G e0}
      (hp : IsProperEdgeColoring G phi) (ho : IsOneEdgeUncolored phi e0)
      (hclosure : TashkinovClosure phi S F) :
      TashkinovClosure sigma S F := by
    as_aux_lemma =>
    have routeTransport (A : TreeSequence G e0)
        (route : TashkinovAugmentationSequence phi A F) :
        TashkinovAugmentationSequence sigma A F :=
      TashkinovAugmentationSequence.transport_of_stable hstable route
    refine ⟨routeTransport S hclosure.1, ?_⟩
    intro f c v hf hv hfc hcv
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨u, hu, w, hw, hend⟩ := hf
    have hincident : TreeIncidentEdge F f := by
      refine ⟨u, hu, ?_⟩
      simp [Incident, hend]
    have hcphi : c ∈ MissingColors G phi v := by
      rw [← hstable.2 v hv]
      exact hcv
    have hcF : c ∈ TreeMissingColors phi F :=
      Finset.mem_biUnion.mpr ⟨v, hv, hcphi⟩
    have hfixed := (sc1 G e0 F D phi sigma hp ho hproper hone).mp hstable
      f hincident (Or.inr ⟨c, Finset.mem_union_left D hcF, hfc⟩)
    have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet F) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, hu, w, hw, hend⟩
    exact hclosure.2 hboundary hv (hfixed.symm.trans hfc) hcphi
  have cert := original.series.certified n
  generalize hn : n = target at cert
  have facts : IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
      TreeSequenceInitialSegment Tn F ∧ Tn.length < F.length ∧
      ((original.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovClosure sigma Tn F) ∨
        ((original.series.data.kind n = some TashkinovExtensionKind.SE ∨
            original.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            original.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovClosure sigma seed F)) := by
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hzero : original.rounds = 0 := congrArg Fin.val hn
      have := original.roundsPositive
      omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hvals := congrArg Fin.val hn
        simp only [n, Fin.val_last, Fin.val_succ] at hvals
        dsimp [q]
        omega
      subst i
      have hp : IsProperEdgeColoring G phi := by
        simpa [phi, ← hq, currentColoring] using choice.selectedProper
      have ho : IsOneEdgeUncolored phi e0 := by
        simpa [phi, ← hq, currentColoring] using choice.selectedOneUncolored
      refine ⟨hp, ho, ?_, ?_, Or.inr ⟨Or.inl ?_, choice.edge,
        adjoined, ?_, ?_, ?_⟩⟩
      · simpa only [Tn, F, hq, hnFinal] using orderedExtension
      · simpa only [Tn, F, hq, hnFinal] using strictExtension
      · simpa [hq] using currentKind
      · simpa [hq] using currentEdges
      · simpa [Tn, hq] using adjoinedExactly
      · exact transport hp ho (by simpa only [phi, F, hq, hnFinal] using closedExtension)
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension
        orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hvals := congrArg Fin.val hn
        simp only [n, Fin.val_last, Fin.val_succ] at hvals
        dsimp [q]
        omega
      subst i
      have hp : IsProperEdgeColoring G phi := by simpa [phi, hq] using currentProper
      have ho : IsOneEdgeUncolored phi e0 := by simpa [phi, hq] using currentOneUncolored
      refine ⟨hp, ho, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
      · simpa only [Tn, F, hq, hnFinal] using orderedExtension
      · simpa only [Tn, F, hq, hnFinal] using strictExtension
      · simpa [hq] using currentKind
      · exact transport hp ho (by simpa only [phi, Tn, F, hq, hnFinal] using closedExtension)
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hvals := congrArg Fin.val hn
        simp only [n, Fin.val_last, Fin.val_succ] at hvals
        dsimp [q]
        omega
      subst i
      have hp : IsProperEdgeColoring G phi := by
        simpa [phi, ← hq, currentColoring] using previousProper
      have ho : IsOneEdgeUncolored phi e0 := by
        simpa [phi, ← hq, currentColoring] using previousOneUncolored
      refine ⟨hp, ho, ?_, ?_, Or.inr ⟨Or.inr ?_, available.edge,
        adjoined, ?_, ?_, ?_⟩⟩
      · simpa only [Tn, F, hq, hnFinal] using orderedExtension
      · simpa only [Tn, F, hq, hnFinal] using strictExtension
      · simpa [hq] using currentKind
      · simpa [hq] using currentEdges
      · simpa [Tn, hq] using adjoinedExactly
      · exact transport hp ho (by simpa only [phi, F, hq, hnFinal] using closedExtension)
  have hsubset := TreeSequenceInitialSegmentVertexSetSubset facts.2.2.1
  have ladderStable : StableColoring Tn D phi sigma :=
    hstable.mono hsubset (fun _ member => member)
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1,
    ladderStable, facts.2.2.2.2⟩

end GoldbergSeymour

end
