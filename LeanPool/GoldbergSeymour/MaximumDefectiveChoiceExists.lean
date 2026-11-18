/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max

public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed

public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice

/-!
# Maximum Defective Choice Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem MaximumDefectiveChoiceExists {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : Nat} (e0 : E)
    (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (hnotStrong :
      ¬ ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T)) :
    Nonempty (MaximumDefectiveChoice G e0 T C phi) := by
  classical
  let X := TreeSequenceVertexSet T
  have hrepeat : exists f g c,
      f ∈ BoundaryEdges G X ∧ g ∈ BoundaryEdges G X ∧ f ≠ g ∧
        phi f = some c ∧ phi g = some c := by
    unfold ColoredVertexSetStronglyClosed at hnotStrong
    push Not at hnotStrong
    exact hnotStrong hclosed
  obtain ⟨f, g, c, hf, hg, hfg, hfc, hgc⟩ := hrepeat
  have hfcolor : f ∈ BoundaryColorEdges G phi X c := by
    simp [BoundaryColorEdges, hf, hfc]
  have hgcolor : g ∈ BoundaryColorEdges G phi X c := by
    simp [BoundaryColorEdges, hg, hgc]
  have hcdef : DefectiveColor G phi X c := by
    unfold DefectiveColor
    have hsubset : ({f, g} : Finset E) ⊆ BoundaryColorEdges G phi X c := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hfcolor
      · exact hgcolor
    have hcard : ({f, g} : Finset E).card = 2 := by simp [hfg]
    rw [← hcard]
    exact Finset.card_le_card hsubset
  obtain ⟨v, hvX, u, huX, hfends⟩ := by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using hf
  have hfdef : DefectiveEdge G phi X f := ⟨c, hcdef, hfcolor⟩
  have hvf : Incident G v f := by
    change v ∈ G.ends f
    rw [hfends]
    simp
  have hvdef : DefectiveVertex G phi X v := ⟨hvX, f, hfdef, hvf⟩
  let eligible : Finset (Fin (T.length + 1)) := Finset.univ.filter fun i =>
    exists pi : PartialEdgeColoring E k,
      IsProperEdgeColoring G pi ∧ IsOneEdgeUncolored pi e0 ∧
        StableColoring T C phi pi ∧ DefectiveVertex G pi X (T.vertex i)
  have hvindex : exists i : Fin (T.length + 1), T.vertex i = v := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image] at hvX
    obtain ⟨i, _, hi⟩ := hvX
    exact ⟨i, hi⟩
  obtain ⟨iv, hiv⟩ := hvindex
  have hivEligible : iv ∈ eligible := by
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨phi, hproper, hone, ?_, ?_⟩
    · unfold StableColoring
      exact ⟨by intros; rfl, by intros; rfl⟩
    · simpa [hiv] using hvdef
  have heligible : eligible.Nonempty := ⟨iv, hivEligible⟩
  let imax : Fin (T.length + 1) := eligible.max' heligible
  have himaxEligible : imax ∈ eligible := Finset.max'_mem eligible heligible
  obtain ⟨selected, hselectedProper, hselectedOne, hselectedStable,
      hselectedDefective⟩ := by
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
      using himaxEligible
  obtain ⟨edge, hedgeDefective, hedgeIncident⟩ := hselectedDefective.2
  obtain ⟨color, hcolorDefective, hedgeColorMem⟩ := hedgeDefective
  have hedgeBoundary : edge ∈ BoundaryEdges G X := by
    exact (Finset.mem_filter.mp hedgeColorMem).1
  have hedgeColor : selected edge = some color := by
    exact (Finset.mem_filter.mp hedgeColorMem).2
  obtain ⟨inside, hinsideX, outside, houtsideX, hedgeEnds⟩ := by
    simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using hedgeBoundary
  have hvertexEq : T.vertex imax = inside := by
    have hmem : T.vertex imax = inside ∨ T.vertex imax = outside := by
      change T.vertex imax ∈ G.ends edge at hedgeIncident
      rw [hedgeEnds] at hedgeIncident
      simpa using hedgeIncident
    rcases hmem with h | h
    · exact h
    · exact (houtsideX (h ▸ hselectedDefective.1)).elim
  refine ⟨{
    selected := selected
    selectedProper := hselectedProper
    selectedOneUncolored := hselectedOne
    selectedStable := hselectedStable
    vertex := T.vertex imax
    vertexDefective := hselectedDefective
    maximal := ?_
    edge := edge
    edgeDefective := ⟨color, hcolorDefective, hedgeColorMem⟩
    edgeIncident := hedgeIncident
    otherEndpoint := outside
    otherOutside := houtsideX
    edgeEnds := by simpa [hvertexEq] using hedgeEnds
    color := color
    edgeColor := hedgeColor }⟩
  intro pi w hpiProper hpiOne hpiStable hwDefective
  have hwX := hwDefective.1
  obtain ⟨iw, hiw⟩ : exists iw : Fin (T.length + 1), T.vertex iw = w := by
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hwX
    obtain ⟨iw, _, hiw⟩ := hwX
    exact ⟨iw, hiw⟩
  have hiwEligible : iw ∈ eligible := by
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨pi, hpiProper, hpiOne, hpiStable, by simpa [hiw] using hwDefective⟩
  have hiwLe : iw ≤ imax := Finset.le_max' eligible iw hiwEligible
  rcases hiwLe.eq_or_lt with hEq | hLt
  · left
    simpa [hiw] using congrArg T.vertex hEq
  · right
    exact ⟨iw, imax, hiw, rfl, hLt⟩

end GoldbergSeymour

end
