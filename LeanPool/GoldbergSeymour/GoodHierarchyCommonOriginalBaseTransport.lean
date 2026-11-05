/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesColoringProperties

public import LeanPool.GoldbergSeymour.HierarchyBaseCorrespondingTransport

public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Good Hierarchy Common Original Base Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyCommonOriginalBaseTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    ∃ baseU : HierarchyBase corrU.replacementETT sigma,
      baseU.core = baseJ.core ∧
      baseU.closure = baseJ.closure ∧
      baseU.supportPosition.val = baseJ.supportPosition.val := by
  classical
  rcases corrJ with ⟨replacementInputJ, replacementSeriesJ, replacementETTJ,
    rungAgreementJ, seriesPresentationJ, finalGeneratingColoringJ,
    ladderTreesAgreeJ, storedColorsAgreeJ, connectingEdgesAgreeJ,
    extensionKindsAgreeJ, replacementProperJ, replacementOneUncoloredJ,
    replacementStableJ⟩
  cases replacementETTJ with
  | mk roundsJ roundsPositiveJ replacementDataJ aboveJ strictJ belowJ generatingJ =>
    cases rungAgreementJ
    have seriesSameJ : replacementDataJ = replacementSeriesJ :=
      eq_of_heq seriesPresentationJ
    cases seriesSameJ
    rcases corrU with ⟨replacementInputU, replacementSeriesU, replacementETTU,
      rungAgreementU, seriesPresentationU, finalGeneratingColoringU,
      ladderTreesAgreeU, storedColorsAgreeU, connectingEdgesAgreeU,
      extensionKindsAgreeU, replacementProperU, replacementOneUncoloredU,
      replacementStableU⟩
    cases replacementETTU with
    | mk roundsU roundsPositiveU replacementDataU aboveU strictU belowU generatingU =>
      cases rungAgreementU
      have seriesSameU : replacementDataU = replacementSeriesU :=
        eq_of_heq seriesPresentationU
      cases seriesSameU
      let corrJU : CorrespondingExtendedTashkinovTree G k e0
          { rounds := ett.rounds
            roundsPositive := roundsPositiveJ
            series := replacementSeriesJ
            abovePenultimate := aboveJ
            strictAbovePenultimate := strictJ
            belowFinal := belowJ
            generatingColoring := generatingJ }
          sigma U := {
        replacementInput := replacementInputU
        replacementSeries := replacementSeriesU
        replacementETT := {
          rounds := ett.rounds
          roundsPositive := roundsPositiveU
          series := replacementSeriesU
          abovePenultimate := aboveU
          strictAbovePenultimate := strictU
          belowFinal := belowU
          generatingColoring := generatingU }
        rungAgreement := rfl
        seriesPresentation := by rfl
        finalGeneratingColoring := finalGeneratingColoringU
        ladderTreesAgree := by
          intro i
          exact (ladderTreesAgreeU i).trans (ladderTreesAgreeJ i).symm
        storedColorsAgree := by
          intro i
          exact (storedColorsAgreeU i).trans (storedColorsAgreeJ i).symm
        connectingEdgesAgree := by
          intro i
          exact (connectingEdgesAgreeU i).trans (connectingEdgesAgreeJ i).symm
        extensionKindsAgree := by
          intro i
          exact (extensionKindsAgreeU i).trans (extensionKindsAgreeJ i).symm
        replacementProper := replacementProperU
        replacementOneUncolored := replacementOneUncoloredU
        replacementStable := by
          intro i
          have treeMissingEq : TreeMissingColors
                (replacementSeriesJ.data.coloring i.succ)
                (replacementSeriesJ.data.tree i.succ.castSucc) =
              TreeMissingColors (ett.series.data.coloring i.succ)
                (ett.series.data.tree i.succ.castSucc) := by
            rw [ladderTreesAgreeJ i]
            ext c
            simp only [TreeMissingColors, Finset.mem_biUnion]
            constructor
            · rintro ⟨v, hv, hc⟩
              exact ⟨v, hv, by
                rw [← (replacementStableJ i).2 v hv]
                exact hc⟩
            · rintro ⟨v, hv, hc⟩
              exact ⟨v, hv, by
                rw [(replacementStableJ i).2 v hv]
                exact hc⟩
          have storedEq :
              TashkinovStoredColors replacementSeriesJ.data i.succ =
                TashkinovStoredColors ett.series.data i.succ := by
            have nonzero : (i.succ : Fin (ett.rounds + 1)).val ≠ 0 := by
              simp
            unfold TashkinovStoredColors
            simp only [ite_eq_right nonzero]
            ext c
            simp only [Finset.mem_sdiff, Finset.mem_biUnion]
            constructor
            · rintro ⟨⟨h, hh, hc⟩, hn⟩
              refine ⟨⟨h, hh, ?_⟩, ?_⟩
              · by_cases hle : h.val ≤ i.succ.val
                · simp only [ite_eq_left hle] at hc ⊢
                  simpa [storedColorsAgreeJ h] using hc
                · simp only [ite_eq_right hle] at hc ⊢
                  exact hc
              · rw [treeMissingEq] at hn
                exact hn
            · rintro ⟨⟨h, hh, hc⟩, hn⟩
              refine ⟨⟨h, hh, ?_⟩, ?_⟩
              · by_cases hle : h.val ≤ i.succ.val
                · simp only [ite_eq_left hle] at hc ⊢
                  simpa [storedColorsAgreeJ h] using hc
                · simp only [ite_eq_right hle] at hc ⊢
                  exact hc
              · rw [← treeMissingEq] at hn
                exact hn
          have originalGood :
              IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧
                IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 := by
            exact ett.series.coloringProperties i.succ
          have jGood :
              IsProperEdgeColoring G (replacementSeriesJ.data.coloring i.succ) ∧
                IsOneEdgeUncolored (replacementSeriesJ.data.coloring i.succ) e0 :=
            ⟨replacementProperJ i.succ, replacementOneUncoloredJ i.succ⟩
          have uGood :
              IsProperEdgeColoring G (replacementSeriesU.data.coloring i.succ) ∧
                IsOneEdgeUncolored (replacementSeriesU.data.coloring i.succ) e0 :=
            ⟨replacementProperU i.succ, replacementOneUncoloredU i.succ⟩
          rw [ladderTreesAgreeJ i, storedEq]
          exact (sc2 G e0 (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.succ)).trans
            (x := ⟨replacementSeriesJ.data.coloring i.succ, jGood⟩)
            (y := ⟨ett.series.data.coloring i.succ, originalGood⟩)
            (z := ⟨replacementSeriesU.data.coloring i.succ, uGood⟩)
            ((sc2 G e0 (ett.series.data.tree i.succ.castSucc)
              (TashkinovStoredColors ett.series.data i.succ)).symm
              (replacementStableJ i))
            (replacementStableU i) }
      exact HierarchyBaseCorrespondingTransport G k e0 replacementInputJ J U
        sigma
        { rounds := ett.rounds
          roundsPositive := roundsPositiveJ
          series := replacementSeriesJ
          abovePenultimate := aboveJ
          strictAbovePenultimate := strictJ
          belowFinal := belowJ
          generatingColoring := generatingJ }
        corrJU baseJ

end GoldbergSeymour

end
