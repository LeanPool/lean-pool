/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# Terminal Data of Corresponding Extended Trees

Shared facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Corresponding trees have the same terminal ladder tree and extension kind,
even when their final colorings differ. -/
theorem CorrespondingExtendedTashkinovTree.terminalTreeKind.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (sigma : PartialEdgeColoring
    E k) {inp gen : PartialEdgeColoring E k} {U : TreeSequence G e0} (original :
    ExtendedTashkinovTree G k e0 inp U gen) (W : TreeSequence G e0) (c :
    CorrespondingExtendedTashkinovTree G k e0 original sigma W),
    c.replacementETT.series.data.tree (Fin.last c.replacementETT.rounds).castSucc =
    original.series.data.tree (Fin.last original.rounds).castSucc ∧
    c.replacementETT.series.data.kind (Fin.last c.replacementETT.rounds) =
    original.series.data.kind (Fin.last original.rounds) := by
  classical
  intro V E _ _ _ G k e0 sigma inp gen U original W c
  rcases c with ⟨ri, rs, re, hr, hs, hf, ht, hd, he, hk, hp, hu, hst⟩
  cases re with
  | mk rounds positive series above strict below generating =>
    cases hr
    have hseries : series = rs := eq_of_heq hs
    cases hseries
    let i : Fin original.rounds := ⟨original.rounds - 1, by
      have := original.roundsPositive
      omega⟩
    have hi : i.succ = Fin.last original.rounds := by
      apply Fin.ext
      have := original.roundsPositive
      simp [i]
      omega
    exact ⟨by simpa [hi] using ht i, hk _⟩

/-- The final tree is independent of the chosen presentation of the replacement series. -/
theorem CorrespondingExtendedTashkinovTree.finalTreePresentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {U : TreeSequence G e0}
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    corr.replacementETT.series.data.tree (Fin.last (corr.replacementETT.rounds + 1)) =
      corr.replacementSeries.data.tree (Fin.last (ett.rounds + 1)) := by
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hf,
    ht, hd, he, hk, hp, ho, hstable⟩
  cases newETT with
  | mk rounds positive data above strict below generating =>
    cases hr
    have hseries : data = newSeries := eq_of_heq hs
    cases hseries
    rfl

/-- The final replacement coloring is proper and leaves exactly the distinguished edge uncolored. -/
theorem CorrespondingExtendedTashkinovTree.coloringProperties {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {U : TreeSequence G e0}
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 := by
  exact corr.replacementETT.coloringProperties

/-- The terminal replacement coloring is stable on the original penultimate tree. -/
theorem CorrespondingExtendedTashkinovTree.terminalStability {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {U : TreeSequence G e0}
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma := by
  let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
  have hi : i.succ = Fin.last ett.rounds := Fin.ext (by
    dsimp [i]
    have := ett.roundsPositive
    omega)
  have stable := corr.replacementStable i
  simpa only [hi, ← corr.finalGeneratingColoring, ← ett.generatingColoring] using stable

/-- Correspondence preserves the connecting edges of the terminal extension. -/
theorem CorrespondingExtendedTashkinovTree.terminalConnectingEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {U : TreeSequence G e0}
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    corr.replacementETT.series.data.connectingEdges (Fin.last corr.replacementETT.rounds) =
      ett.series.data.connectingEdges (Fin.last ett.rounds) := by
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hf,
    ht, hd, he, hk, hp, ho, hstable⟩
  cases newETT with
  | mk rounds positive data above strict below generating =>
    cases hr
    have hseries : data = newSeries := eq_of_heq hs
    cases hseries
    exact he _

/-- Corresponding extended trees agree on their terminal ladder tree, kind and stored colors. -/
theorem CorrespondingExtendedTashkinovTree.terminalData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {U : TreeSequence G e0}
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind (Fin.last ett.rounds) ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
  classical
  have terminalFacts := CorrespondingExtendedTashkinovTree.terminalTreeKind
    G k e0 sigma ett U corr
  have stability := corr.terminalStability
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hf,
    ht, hd, he, hk, hp, ho, hstable⟩
  cases newETT with
  | mk rounds positive data above strict below generating =>
    cases hr
    have hseries : data = newSeries := eq_of_heq hs
    cases hseries
    have missing : TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
      unfold TreeMissingColors
      apply Finset.biUnion_congr rfl
      exact stability.2
    refine ⟨terminalFacts.1, terminalFacts.2, ?_⟩
    unfold TashkinovStoredColors
    have hn : (Fin.last ett.rounds).val ≠ 0 := by
      have := ett.roundsPositive
      simpa using Nat.ne_of_gt (Nat.zero_lt_of_lt ett.roundsPositive)
    simp only [ite_eq_right hn]
    simp_rw [hd]
    rw [← hf, ← ett.generatingColoring, terminalFacts.1, missing]

end GoldbergSeymour

end
