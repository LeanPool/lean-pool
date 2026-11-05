/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior

/-!
# P2880_T1_Elementary Prefix Swap

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2880_T1_ElementaryPrefixSwap
    {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (mu : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G mu)
    (B X Z : TreeSequence G e0)
    (hBX : TreeSequenceInitialSegment B X)
    (hXZ : TreeSequenceInitialSegment X Z)
    (helementary : ColoredVertexSetElementary G mu (TreeSequenceVertexSet Z))
    (ha : alpha ∈ TreeMissingColors mu B)
    (hb : beta ∈ TreeMissingColors mu B)
    (z : Sum V E)
    (houtside : ∀ v ∈ TreeSequenceVertexSet X,
      Sum.inl v ∉ TwoColorComponent G mu alpha beta z) :
    let sigma := TwoColorComponentSwap G mu alpha beta z
    (∀ v ∈ TreeSequenceVertexSet X, ∀ f : E, Incident G v f →
      sigma f = mu f) ∧
    (∀ v ∈ TreeSequenceVertexSet Z,
      MissingColors G sigma v = MissingColors G mu v) := by
  classical
  let _ := Fintype.ofFinite V
  let Q := TwoColorComponent G mu alpha beta z
  let sigma := TwoColorComponentSwap G mu alpha beta z
  have edgeToVertex {v : V} {f : E} (hf : Sum.inr f ∈ Q)
      (hvf : Incident G v f) (hc : mu f = some alpha ∨ mu f = some beta) :
      Sum.inl v ∈ Q := by
    change (TwoColorIncidenceGraph G mu alpha beta).connectedComponentMk
      (Sum.inr f) = _ at hf
    change (TwoColorIncidenceGraph G mu alpha beta).connectedComponentMk
      (Sum.inl v) = _
    have hadj : (TwoColorIncidenceGraph G mu alpha beta).Adj
        (Sum.inl v) (Sum.inr f) := ⟨hvf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hf
  have vertexToEdge {v : V} {f : E} (hv : Sum.inl v ∈ Q)
      (hvf : Incident G v f) (hc : mu f = some alpha ∨ mu f = some beta) :
      Sum.inr f ∈ Q := by
    change (TwoColorIncidenceGraph G mu alpha beta).connectedComponentMk
      (Sum.inl v) = _ at hv
    change (TwoColorIncidenceGraph G mu alpha beta).connectedComponentMk
      (Sum.inr f) = _
    have hadj : (TwoColorIncidenceGraph G mu alpha beta).Adj
        (Sum.inr f) (Sum.inl v) := ⟨hvf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have behavior := TwoColorComponentSwapMissingBehavior G mu alpha beta hne hproper z
  refine ⟨?_, ?_⟩
  · intro v hv f hvf
    by_cases hf : Sum.inr f ∈ Q
    · by_cases ha : mu f = some alpha
      · exact False.elim (houtside v hv (edgeToVertex hf hvf (Or.inl ha)))
      · by_cases hb : mu f = some beta
        · exact False.elim (houtside v hv (edgeToVertex hf hvf (Or.inr hb)))
        · simp [TwoColorComponentSwap, Q, hf, ha, hb]
    · simp [TwoColorComponentSwap, Q, hf]
  · intro v hvZ
    by_cases hvQ : Sum.inl v ∈ Q
    · have oldNotMissing (c : Fin k) (hc : c ∈ TreeMissingColors mu B) :
          c ∉ MissingColors G mu v := by
        obtain ⟨w, hwB, hcw⟩ := Finset.mem_biUnion.mp hc
        have hwX := TreeSequenceInitialSegmentVertexSetSubset hBX hwB
        have hwZ := TreeSequenceInitialSegmentVertexSetSubset hXZ hwX
        have hwv : w ≠ v := by
          intro heq
          exact houtside w hwX (heq.symm ▸ hvQ)
        exact fun hcv => Finset.disjoint_left.mp
          (helementary hwZ hvZ hwv) hcw hcv
      have hna := oldNotMissing alpha ha
      have hnb := oldNotMissing beta hb
      have presentOfNotMissing (c : Fin k) (hc : c ∉ MissingColors G mu v) :
          ∃ f : E, Incident G v f ∧ mu f = some c := by
        have hp : c ∈ PresentColors G mu v := by
          by_contra hnp
          exact hc (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnp⟩)
        simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] using hp
      obtain ⟨fa, hvfa, hfa⟩ := presentOfNotMissing alpha hna
      obtain ⟨fb, hvfb, hfb⟩ := presentOfNotMissing beta hnb
      have hfaQ := vertexToEdge hvQ hvfa (Or.inl hfa)
      have hfbQ := vertexToEdge hvQ hvfb (Or.inr hfb)
      have hnewB : sigma fa = some beta := by
        simp [sigma, TwoColorComponentSwap, Q, hfaQ, hfa]
      have hnewA : sigma fb = some alpha := by
        simp [sigma, TwoColorComponentSwap, Q, hfbQ, hfb, hne.symm]
      have hsna : alpha ∉ MissingColors G sigma v := by
        intro h
        exact (Finset.mem_sdiff.mp h).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fb, hvfb, hnewA⟩)
      have hsnb : beta ∉ MissingColors G sigma v := by
        intro h
        exact (Finset.mem_sdiff.mp h).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fa, hvfa, hnewB⟩)
      ext c
      by_cases hca : c = alpha
      · subst c
        exact iff_of_false hsna hna
      · by_cases hcb : c = beta
        · subst c
          exact iff_of_false hsnb hnb
        · exact behavior.2.2.2 v c hca hcb
    · exact behavior.1 v hvQ

end GoldbergSeymour

end
