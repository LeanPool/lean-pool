/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTerminalRoute
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

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
  exact ett.series.terminalRouteWithControl (by have := ett.roundsPositive; omega)
    phi ett.generatingColoring T ett.abovePenultimate ett.strictAbovePenultimate ett.belowFinal

/-- A parallel terminal extension gives the route from its penultimate tree. -/
theorem ExtendedTashkinovTree.parallelTerminalRoute {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (parallel : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) :
    TashkinovAugmentationSequence phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) T := by
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with ⟨_, route⟩ | ⟨kind, _⟩
  · exact route
  · rcases kind with kind | kind <;> rw [parallel] at kind <;> cases kind

/-- Colors absent from the terminal control set cannot color its connecting edge. -/
theorem ExtendedTashkinovTree.terminalRouteAvoiding {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi) (alpha beta : Fin k)
    (excluded : ∀ c : Fin k, c = alpha ∨ c = beta →
      c ∉ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∪
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) :
    let n := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn T) ∨
    ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = {f} ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed T ∧
        phi f ≠ some alpha ∧ phi f ≠ some beta) := by
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with route |
    ⟨kind, f, seed, edges, adjoin, _, ⟨c, controlled, colored⟩, route⟩
  · exact Or.inl route
  · have avoid (d : Fin k) (which : d = alpha ∨ d = beta) : phi f ≠ some d := by
      intro equal
      have same := Option.some.inj (colored.symm.trans equal)
      exact excluded d which (same ▸ controlled)
    exact Or.inr ⟨kind, f, seed, edges, adjoin, route,
      avoid alpha (Or.inl rfl), avoid beta (Or.inr rfl)⟩

end GoldbergSeymour

end
