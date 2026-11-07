/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict

/-!
# The last certified extension on a terminal prefix

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The final certified extension supplies its coloring, controlled seed and full closure. -/
theorem TashkinovSeries.terminalCertificate {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (positive : 0 < rounds) (phi : PartialEdgeColoring E k)
    (coloringEqual : phi = series.data.coloring (Fin.last rounds)) :
    let n := Fin.last rounds
    let Tn := series.data.tree n.castSucc
    let Dn := TashkinovStoredColors series.data n
    ∃ seed : TreeSequence G e0,
      IsProperEdgeColoring G phi ∧ IsOneEdgeUncolored phi e0 ∧
      ((series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ∨
        ((series.data.kind n = some TashkinovExtensionKind.SE ∨
            series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ f : E, series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
            TreeIncidentEdge Tn f ∧ ∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c)) ∧
      TashkinovClosure phi seed (series.data.tree (Fin.last (rounds + 1))) := by
  classical
  let n := Fin.last rounds
  let Tn := series.data.tree n.castSucc
  let Dn := TashkinovStoredColors series.data n
  have storedOrMissing (c : Fin k) (hc : c ∈ series.data.stored n) :
      c ∈ TreeMissingColors phi Tn ∪ Dn := by
    by_cases hm : c ∈ TreeMissingColors phi Tn
    · exact Finset.mem_union_left _ hm
    · apply Finset.mem_union_right
      unfold Dn TashkinovStoredColors
      have hn : n.val ≠ 0 := by simpa [n] using Nat.ne_of_gt positive
      simp only [ite_eq_right hn]
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hc]⟩
      · simpa only [← coloringEqual, Tn, n] using hm
  have step := series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hcol : phi = choice.selected := by
      simpa only [← hj, coloring, n] using coloringEqual
    refine ⟨seed, ?_, ?_, Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      ⟨choice.vertex, by simpa [Tn, hj] using choice.vertexDefective.1,
        choice.edgeIncident⟩, choice.color, ?_, ?_⟩, ?_⟩
    · rw [hcol]; exact choice.selectedProper
    · rw [hcol]; exact choice.selectedOneUncolored
    · apply storedOrMissing
      rw [← hj, stored]
      simp
    · rw [hcol]; exact choice.edgeColor
    · simpa [hj, hlast, ← coloringEqual, n] using closure
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hcol : phi = series.data.coloring j.succ := by simpa only [hj] using coloringEqual
    refine ⟨Tn, ?_, ?_, Or.inl ⟨by simpa [hj] using kind, rfl⟩, ?_⟩
    · rw [hcol]; exact proper
    · rw [hcol]; exact one
    · simpa [Tn, hj, hlast, ← coloringEqual, n] using closure
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hcol : phi = series.data.coloring j.castSucc := by
      simpa only [← hj, coloring, n] using coloringEqual
    have hcolors : phi available.edge = some available.gamma ∨
        phi available.edge = some available.delta := by
      simp only [hcol]
      have hadj := available.returnPath.adj_snd
        (SimpleGraph.Walk.not_nil_of_ne (by intro he; cases he))
      cases hh : available.returnPath.snd with
      | inl v =>
        have hc : (TwoColorIncidenceGraph G (series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inl v) :=
          hh ▸ hadj
        exact hc.2
      | inr f =>
        have hc : (TwoColorIncidenceGraph G (series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inr f) :=
          hh ▸ hadj
        exact False.elim hc
    have hincident : TreeIncidentEdge Tn available.edge := by
      refine ⟨available.insideEndpoint, ?_, ?_⟩
      · have hidx : j.castSucc.succ = n.castSucc := Fin.ext (by
          simpa only [Fin.val_succ, Fin.val_castSucc] using congrArg Fin.val hj)
        simpa only [Tn, hidx] using available.insideInCurrent
      · rw [Incident, available.edgeEnds]
        exact Sym2.mem_mk_left _ _
    refine ⟨seed, ?_, ?_, Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin, hincident, ?_⟩, ?_⟩
    · rw [hcol]; exact ‹IsProperEdgeColoring G (series.data.coloring j.castSucc)›
    · rw [hcol]; exact ‹IsOneEdgeUncolored (series.data.coloring j.castSucc) e0›
    · rcases hcolors with hc | hc
      · exact ⟨available.gamma, storedOrMissing _ (by rw [← hj, stored]; simp), hc⟩
      · exact ⟨available.delta, storedOrMissing _ (by rw [← hj, stored]; simp), hc⟩
    · simpa [hj, hlast, ← coloringEqual, n] using closure

/-- A strict terminal prefix retains the connecting edge's incidence and color control. -/
theorem TashkinovSeries.terminalRouteWithControl {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (positive : 0 < rounds) (phi : PartialEdgeColoring E k)
    (coloringEqual : phi = series.data.coloring (Fin.last rounds))
    (B : TreeSequence G e0)
    (TnToB : TreeSequenceInitialSegment (series.data.tree (Fin.last rounds).castSucc) B)
    (TnStrictB : (series.data.tree (Fin.last rounds).castSucc).length < B.length)
    (BToFinal : TreeSequenceInitialSegment B (series.data.tree (Fin.last (rounds + 1)))) :
    let n := Fin.last rounds
    let Tn := series.data.tree n.castSucc
    let Dn := TashkinovStoredColors series.data n
    (series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn B) ∨
    ((series.data.kind n = some TashkinovExtensionKind.SE ∨
        series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0), series.data.connectingEdges n = {f} ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TreeIncidentEdge Tn f ∧
        (∃ c ∈ TreeMissingColors phi Tn ∪ Dn, phi f = some c) ∧
        TashkinovAugmentationSequence phi seed B) := by
  classical
  obtain ⟨seed, _, _, terminal, closure⟩ := series.terminalCertificate positive phi coloringEqual
  rcases terminal with ⟨kind, rfl⟩ | ⟨kind, f, edges, adjoin, incident, control⟩
  · exact Or.inl ⟨kind, TashkinovAugmentationSequenceRestrict phi _ B _ closure.1 TnToB BToFinal⟩
  · have seedBelow : TreeSequenceInitialSegment seed B :=
      TreeSequenceInitialSegment.of_common_extension BToFinal
        (TashkinovAugmentationSequenceInitialSegment phi _ _ closure.1) (by
          have := adjoin.1
          omega)
    exact Or.inr ⟨kind, f, seed, edges, adjoin, incident, control,
      TashkinovAugmentationSequenceRestrict phi seed B _ closure.1 seedBelow BToFinal⟩

/-- A nontrivial terminal prefix retains the last certified extension route. -/
theorem TashkinovSeries.terminalRoute {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (positive : 0 < rounds) (phi : PartialEdgeColoring E k)
    (coloringEqual : phi = series.data.coloring (Fin.last rounds))
    (B : TreeSequence G e0)
    (TnToB : TreeSequenceInitialSegment (series.data.tree (Fin.last rounds).castSucc) B)
    (TnStrictB : (series.data.tree (Fin.last rounds).castSucc).length < B.length)
    (BToFinal : TreeSequenceInitialSegment B
      (series.data.tree (Fin.last (rounds + 1)))) :
    let n := Fin.last rounds
    let Tn := series.data.tree n.castSucc
    (series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn B) ∨
    ((series.data.kind n = some TashkinovExtensionKind.SE ∨
      series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
        TashkinovAugmentationSequence phi seed B) := by
  obtain route | ⟨kind, f, seed, edges, adjoin, _, _, route⟩ :=
    series.terminalRouteWithControl positive phi coloringEqual B TnToB TnStrictB BToFinal
  · exact Or.inl route
  · exact Or.inr ⟨kind, f, seed, edges, adjoin, route⟩

/-- Recolor a terminal route across a one-edge prefix using its actual local invariants. -/
theorem TashkinovSeries.terminalRouteColoringTransport {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (positive : 0 < rounds) (phi : PartialEdgeColoring E k)
    (coloringEqual : phi = series.data.coloring (Fin.last rounds)) (B : TreeSequence G e0)
    (TnToB : TreeSequenceInitialSegment (series.data.tree (Fin.last rounds).castSucc) B)
    (TnStrictB : (series.data.tree (Fin.last rounds).castSucc).length < B.length)
    (BToFinal : TreeSequenceInitialSegment B (series.data.tree (Fin.last (rounds + 1))))
    (sigma : PartialEdgeColoring E k) (before : TreeSequence G e0)
    (initial : TreeSequenceInitialSegment before B) (oneEdge : B.length = before.length + 1)
    (fixed : ∀ t : Fin B.length,
      (series.data.tree (Fin.last rounds).castSucc).length ≤ t.val →
        sigma (B.edge t) = phi (B.edge t))
    (missing : ∀ v ∈ TreeSequenceVertexSet before,
      MissingColors G sigma v = MissingColors G phi v) :
    let n := Fin.last rounds
    let Tn := series.data.tree n.castSucc
    (series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma Tn B) ∨
    ((series.data.kind n = some TashkinovExtensionKind.SE ∨
        series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0), series.data.connectingEdges n = {f} ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed B) := by
  rcases series.terminalRoute positive phi coloringEqual B TnToB TnStrictB BToFinal with
    ⟨kind, route⟩ | ⟨kind, f, seed, edges, adjoin, route⟩
  · exact Or.inl ⟨kind, TashkinovAugmentationSequenceColoringTransport phi sigma _ before B
      route initial oneEdge fixed missing⟩
  · exact Or.inr ⟨kind, f, seed, edges, adjoin,
      TashkinovAugmentationSequenceColoringTransport phi sigma seed before B
        route initial oneEdge (fun t afterSeed => fixed t (by have := adjoin.1; omega)) missing⟩

end GoldbergSeymour

end
