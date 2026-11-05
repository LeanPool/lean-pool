/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

/-!
# P2813_T1_Terminal Route

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem P2813_T1_TerminalRoute {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) :
    let n := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn T) ∨
    ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = {f} ∧
        TreeSequenceAdjoinEdge Tn f seed ∧
        TreeIncidentEdge Tn f ∧
        (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
        TashkinovAugmentationSequence phi seed T) := by
  classical
  let n := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
        (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have storedOrMissing (c : Fin k) (hc : c ∈ ett.series.data.stored n) :
      c ∈ TreeMissingColors phi Tn ∪ Dn := by
    by_cases hm : c ∈ TreeMissingColors phi Tn
    · exact Finset.mem_union_left _ hm
    · apply Finset.mem_union_right
      unfold Dn TashkinovStoredColors
      have hn : n.val ≠ 0 := by dsimp [n]; have := ett.roundsPositive; omega
      simp only [ite_eq_right hn]
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hc]⟩
      · simpa only [← ett.generatingColoring, Tn, n] using hm
  have step := ett.series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := ett.roundsPositive; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedT : TreeSequenceInitialSegment seed T :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        ett.belowFinal (by
          have hl := adjoin.1; rw [hj] at hl
          change seed.length = Tn.length + 1 at hl
          have hs := ett.strictAbovePenultimate
          change Tn.length < T.length at hs
          omega)
    have hcol : phi choice.edge = some choice.color := by
      have hg : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hg] using choice.edgeColor
    have hc : choice.color ∈ ett.series.data.stored n := by rw [← hj, stored]; simp
    exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      ⟨choice.vertex, by simpa [Tn, hj] using choice.vertexDefective.1,
        choice.edgeIncident⟩,
      ⟨choice.color, storedOrMissing choice.color hc, hcol⟩,
      TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal⟩
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
    apply TashkinovAugmentationSequenceRestrict phi Tn T _ _ ett.abovePenultimate ett.belowFinal
    simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedT : TreeSequenceInitialSegment seed T :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        ett.belowFinal (by
          have hl := adjoin.1; rw [hj] at hl
          change seed.length = Tn.length + 1 at hl
          have hs := ett.strictAbovePenultimate
          change Tn.length < T.length at hs
          omega)
    have hcol : phi available.edge = some available.gamma ∨
        phi available.edge = some available.delta := by
      have hg : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simp only [hg]
      have hadj := available.returnPath.adj_snd
        (SimpleGraph.Walk.not_nil_of_ne (by intro he; cases he))
      cases hh : available.returnPath.snd with
      | inl v =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inl v) :=
          hh ▸ hadj
        exact hc.2
      | inr f =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inr f) :=
          hh ▸ hadj
        exact False.elim hc
    have hcontrol : ∃ c, phi available.edge = some c ∧
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      rcases hcol with h | h
      · exact ⟨available.gamma, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
      · exact ⟨available.delta, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
    have hincident : TreeIncidentEdge Tn available.edge := by
      refine ⟨available.insideEndpoint, ?_, ?_⟩
      · have hidx : j.castSucc.succ = n.castSucc := Fin.ext (by
          simpa only [Fin.val_succ, Fin.val_castSucc] using congrArg Fin.val hj)
        simpa only [Tn, hidx] using available.insideInCurrent
      · rw [Incident, available.edgeEnds]
        exact Sym2.mem_mk_left _ _
    exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin, hincident,
      by obtain ⟨c, hcol, hc⟩ := hcontrol; exact ⟨c, hc, hcol⟩,
      TashkinovAugmentationSequenceRestrict phi seed T _ hroute hseedT ett.belowFinal⟩

end GoldbergSeymour

end
