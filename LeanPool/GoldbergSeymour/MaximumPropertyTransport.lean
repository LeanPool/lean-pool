/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.ModColoring

public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Maximum Property Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MaximumPropertyTransport {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating)
    (sigmaN : PartialEdgeColoring E k) (_ : ModColoring base sigmaN)
    (Tstar : TreeSequence G e0)
    (corr : CorrespondingExtendedTashkinovTree G k e0 base sigmaN Tstar)
    (hMP : MaximumProperty base) : MaximumProperty corr.replacementETT := by
  classical
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT, rungAgreement,
    seriesPresentation, finalGeneratingColoring, ladderTreesAgree, storedColorsAgree,
    connectingEdgesAgree, extensionKindsAgree, replacementProper,
    replacementOneUncolored, replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have seriesSame : replacementData = replacementSeries := eq_of_heq seriesPresentation
    cases seriesSame
    unfold MaximumProperty
    constructor
    · have firstTree := ladderTreesAgree ⟨0, Nat.zero_lt_of_lt base.roundsPositive⟩
      have firstIndex : (1 : Fin (base.rounds + 2)) =
          (⟨0, Nat.zero_lt_of_lt base.roundsPositive⟩ : Fin base.rounds).succ.castSucc :=
        Fin.ext (by rfl)
      have firstTree' : replacementSeries.data.tree 1 = base.series.data.tree 1 := by
        rw [firstIndex]
        exact firstTree
      exact (congrArg (fun x => (TreeSequenceVertexSet x).card) firstTree').trans hMP.1
    · intro i hi hlast
      dsimp
      intro pi seed candidate proper one stable premise closure
      have hlastBase : i < base.rounds := by simpa using hlast
      have indexValue : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      let idx : Fin (base.rounds + 1) := ⟨i, by omega⟩
      let q : Fin base.rounds := ⟨i - 1, by omega⟩
      have idxSucc : idx = q.succ := by
        apply Fin.ext
        simp [idx, q, indexValue]
      have treeEq : replacementSeries.data.tree idx.castSucc =
          base.series.data.tree idx.castSucc := by
        have ladder := ladderTreesAgree ⟨i - 1, by omega⟩
        simpa [idx, indexValue] using ladder
      have stableBridge := replacementStable q
      have missingEq : ∀ v ∈ TreeSequenceVertexSet
          (base.series.data.tree idx.castSucc),
          MissingColors G (replacementSeries.data.coloring idx) v =
            MissingColors G (base.series.data.coloring idx) v := by
        rw [idxSucc]
        intro v hv
        exact stableBridge.2 v hv
      have treeMissingEq : TreeMissingColors
          (replacementSeries.data.coloring idx)
          (replacementSeries.data.tree idx.castSucc) =
          TreeMissingColors (base.series.data.coloring idx)
            (base.series.data.tree idx.castSucc) := by
        rw [treeEq]
        ext c
        simp only [TreeMissingColors, Finset.mem_biUnion]
        constructor
        · rintro ⟨v, hv, hc⟩
          exact ⟨v, hv, by rw [← missingEq v hv]; exact hc⟩
        · rintro ⟨v, hv, hc⟩
          exact ⟨v, hv, by rw [missingEq v hv]; exact hc⟩
      have storedEq : TashkinovStoredColors replacementSeries.data idx =
          TashkinovStoredColors base.series.data idx := by
        have nonzero : ¬ i = 0 := by omega
        dsimp [idx]
        unfold TashkinovStoredColors
        simp only [ite_eq_right nonzero]
        ext c
        simp only [Finset.mem_sdiff, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨h, hh, hc⟩, hn⟩
          refine ⟨⟨h, hh, ?_⟩, ?_⟩
          · by_cases hle : h.val ≤ i
            · simp only [ite_eq_left hle] at hc ⊢
              simpa [storedColorsAgree h] using hc
            · simp only [ite_eq_right hle] at hc ⊢
              exact hc
          · rw [treeMissingEq] at hn
            exact hn
        · rintro ⟨⟨h, hh, hc⟩, hn⟩
          refine ⟨⟨h, hh, ?_⟩, ?_⟩
          · by_cases hle : h.val ≤ i
            · simp only [ite_eq_left hle] at hc ⊢
              simpa [storedColorsAgree h] using hc
            · simp only [ite_eq_right hle] at hc ⊢
              exact hc
          · rw [← treeMissingEq] at hn
            exact hn
      have baseGood : IsProperEdgeColoring G (base.series.data.coloring idx) ∧
          IsOneEdgeUncolored (base.series.data.coloring idx) e0 := by
        have allGood : ∀ j : Fin base.rounds,
            IsProperEdgeColoring G (base.series.data.coloring j.succ) ∧
              IsOneEdgeUncolored (base.series.data.coloring j.succ) e0 := by
          intro j
          exact base.series.coloringProperties j.succ
        rw [idxSucc]
        exact allGood q
      have baseStable : StableColoring
          (base.series.data.tree idx.castSucc)
          (TashkinovStoredColors base.series.data idx)
          (base.series.data.coloring idx) pi := by
        have bridgeStable : StableColoring
            (base.series.data.tree idx.castSucc)
            (TashkinovStoredColors base.series.data idx)
            (base.series.data.coloring idx) (replacementSeries.data.coloring idx) := by
          repeat rw [idxSucc]
          exact stableBridge
        have replacementToPi : StableColoring
            (base.series.data.tree idx.castSucc)
            (TashkinovStoredColors base.series.data idx)
            (replacementSeries.data.coloring idx) pi := by
          rw [← treeEq]
          rw [← storedEq]
          repeat rw [idxSucc]
          have qSuccIndex : q.succ = (⟨i, by omega⟩ : Fin (base.rounds + 1)) := by
            apply Fin.ext
            simp [q, indexValue]
          have stable' := stable
          repeat rw [← qSuccIndex] at stable'
          have qTreeIndex : q.succ.castSucc =
              (⟨i, by omega⟩ : Fin (base.rounds + 2)) := Fin.ext (by simp [q, indexValue])
          rw [← qTreeIndex] at stable'
          exact stable'
        exact (sc2 G e0 (base.series.data.tree idx.castSucc)
          (TashkinovStoredColors base.series.data idx)).trans
          (x := ⟨base.series.data.coloring idx, baseGood⟩)
          (y := ⟨replacementSeries.data.coloring idx,
            ⟨replacementProper idx, replacementOneUncolored idx⟩⟩)
          (z := ⟨pi, ⟨proper, one⟩⟩) bridgeStable replacementToPi
      have basePremise :
          (base.series.data.kind idx = some TashkinovExtensionKind.PE ∧
              seed = base.series.data.tree idx.castSucc) ∨
            ((base.series.data.kind idx = some TashkinovExtensionKind.SE ∨
                base.series.data.kind idx = some TashkinovExtensionKind.RE) ∧
              ∃ f, base.series.data.connectingEdges idx = {f} ∧
                TreeSequenceAdjoinEdge (base.series.data.tree idx.castSucc) f seed) := by
        rcases premise with premise | premise
        · left
          constructor
          · rw [← extensionKindsAgree idx]
            simpa [idx] using premise.1
          · rw [← treeEq]
            exact premise.2
        · right
          constructor
          · rw [← extensionKindsAgree idx]
            simpa [idx] using premise.1
          · rcases premise.2 with ⟨f, edgeSet, seedDef⟩
            refine ⟨f, ?_, ?_⟩
            · rw [← connectingEdgesAgree idx]
              simpa [idx] using edgeSet
            · rw [← treeEq]
              exact seedDef
      have bound := hMP.2 i hi hlastBase pi seed candidate proper one baseStable
        basePremise closure
      have nextTree := ladderTreesAgree ⟨i, hlastBase⟩
      have nextIndex : (⟨i + 1, by omega⟩ : Fin (base.rounds + 2)) =
          (⟨i, hlastBase⟩ : Fin base.rounds).succ.castSucc := Fin.ext (by rfl)
      have nextTree' : replacementSeries.data.tree ⟨i + 1, by omega⟩ =
          base.series.data.tree ⟨i + 1, by omega⟩ := by
        rw [nextIndex]
        exact nextTree
      rw [nextTree']
      exact bound

end GoldbergSeymour

end
