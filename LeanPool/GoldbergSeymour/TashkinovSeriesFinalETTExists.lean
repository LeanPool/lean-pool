/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# Tashkinov Series Final ETTExists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovSeriesFinalETTExists
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (hrounds : 0 < rounds) :
    exists ett : ExtendedTashkinovTree G k e0 input
        (series.data.tree (Fin.last (rounds + 1)))
        (series.data.coloring (Fin.last rounds)),
      ett.rounds = rounds ∧ HEq ett.series series := by
  classical
  have stepFacts :
    ∀ r : Fin rounds, TreeSequenceInitialSegment (series.data.tree r.succ.castSucc)
        (series.data.tree r.succ.succ) ∧ (series.data.tree r.succ.castSucc).length <
        (series.data.tree r.succ.succ).length := by
    intro r
    have fact := series.certified r.succ
    generalize hi : r.succ = z at fact ⊢
    cases fact with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      simp_all
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
  let r : Fin rounds := ⟨rounds - 1, by omega⟩
  have hpen : r.succ.castSucc = (⟨rounds, by omega⟩ : Fin (rounds + 2)) := by
    apply Fin.ext
    simp [r]
    omega
  have hfinal : r.succ.succ = Fin.last (rounds + 1) := by
    apply Fin.ext
    simp [r]
    omega
  have terminalOrdered : TreeSequenceInitialSegment
      (series.data.tree ⟨rounds, by omega⟩)
      (series.data.tree (Fin.last (rounds + 1))) := by
    rw [← hpen, ← hfinal]
    exact (stepFacts r).1
  have terminalStrict :
      (series.data.tree ⟨rounds, by omega⟩).length <
        (series.data.tree (Fin.last (rounds + 1))).length := by
    rw [← hpen, ← hfinal]
    exact (stepFacts r).2
  let ett : ExtendedTashkinovTree G k e0 input
      (series.data.tree (Fin.last (rounds + 1)))
      (series.data.coloring (Fin.last rounds)) := {
    rounds := rounds
    roundsPositive := hrounds
    series := series
    abovePenultimate := terminalOrdered
    strictAbovePenultimate := terminalStrict
    belowFinal := ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
    generatingColoring := rfl }
  exact ⟨ett, rfl, HEq.rfl⟩

end GoldbergSeymour

end
