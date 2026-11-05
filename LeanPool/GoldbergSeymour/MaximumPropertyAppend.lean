/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumProperty

public import LeanPool.GoldbergSeymour.TashkinovSeriesFinalETTExists
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsAppend
public import LeanPool.GoldbergSeymour.TerminalClosureMaximum

/-!
# Maximum Property Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MaximumPropertyAppend
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hterminal : TerminalClosureMaximum ett)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (extended : TashkinovSeries G k (ett.rounds + 1) e0 input)
    (happend : extended.data =
      TashkinovSeriesDataAppend ett.series.data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma) :
    exists newETT : ExtendedTashkinovTree G k e0 input
        (extended.data.tree (Fin.last ((ett.rounds + 1) + 1)))
        (extended.data.coloring (Fin.last (ett.rounds + 1))),
      newETT.rounds = ett.rounds + 1 /\
      HEq newETT.series extended /\
      MaximumProperty newETT := by
  classical
  obtain ⟨newETT, hrounds, hseries⟩ :=
    TashkinovSeriesFinalETTExists G k (ett.rounds + 1) e0 input extended (by omega)
  refine ⟨newETT, hrounds, hseries, ?_⟩
  cases newETT with
  | mk newRounds newRoundsPositive newSeries above strict below generatingEq =>
    dsimp at hrounds
    subst newRounds
    have seriesEq : newSeries = extended := eq_of_heq hseries
    subst newSeries
    rcases hMP with ⟨hfirst, hold⟩
    unfold MaximumProperty
    constructor
    · let oldOne : Fin (ett.rounds + 2) := ⟨1, by omega⟩
      let newOne : Fin ((ett.rounds + 1) + 2) := ⟨1, by omega⟩
      have oneEq : newOne = oldOne.castSucc := by ext; rfl
      have firstTree : extended.data.tree newOne =
          ett.series.data.tree oldOne := by
        rw [happend, oneEq]
        simp [TashkinovSeriesDataAppend]
      rw [firstTree]
      simpa [newOne, oldOne] using hfirst
    · intro i hi hlast
      dsimp
      intro pi seed candidate proper one stable seedRoute closure
      by_cases hiold : i < ett.rounds
      · let oldIdx : Fin (ett.rounds + 1) := ⟨i, by omega⟩
        let newIdx : Fin ((ett.rounds + 1) + 1) := ⟨i, by omega⟩
        let oldNext : Fin (ett.rounds + 2) := ⟨i + 1, by omega⟩
        let newNext : Fin ((ett.rounds + 1) + 2) := ⟨i + 1, by omega⟩
        have indexEq : newIdx = oldIdx.castSucc := by ext; rfl
        have treeIndexEq : newIdx.castSucc = oldIdx.castSucc.castSucc := by
          rw [indexEq]
        have nextIndexEq : newNext = oldNext.castSucc := by ext; rfl
        have treeEq : extended.data.tree newIdx.castSucc =
            ett.series.data.tree oldIdx.castSucc := by
          rw [happend, treeIndexEq]
          simp [TashkinovSeriesDataAppend]
        have coloringEq : extended.data.coloring newIdx =
            ett.series.data.coloring oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have kindEq : extended.data.kind newIdx = ett.series.data.kind oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have edgesEq : extended.data.connectingEdges newIdx =
            ett.series.data.connectingEdges oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have storedEq : TashkinovStoredColors extended.data newIdx =
            TashkinovStoredColors ett.series.data oldIdx := by
          rw [happend, indexEq]
          have h := TashkinovStoredColorsAppend ett.series.data newTree newColoring
            newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
            newDelta newGamma oldIdx
          exact h
        have nextEq : extended.data.tree newNext = ett.series.data.tree oldNext := by
          rw [happend, nextIndexEq]
          simp [TashkinovSeriesDataAppend]
        have stableOld : StableColoring (ett.series.data.tree oldIdx.castSucc)
            (TashkinovStoredColors ett.series.data oldIdx)
            (ett.series.data.coloring oldIdx) pi := by
          rw [← treeEq, ← storedEq, ← coloringEq]
          simpa [newIdx] using stable
        have routeOld :
            (ett.series.data.kind oldIdx = some TashkinovExtensionKind.PE /\
              seed = ett.series.data.tree oldIdx.castSucc) \/
            ((ett.series.data.kind oldIdx = some TashkinovExtensionKind.SE \/
                ett.series.data.kind oldIdx = some TashkinovExtensionKind.RE) /\
              exists f : E, ett.series.data.connectingEdges oldIdx = {f} /\
                TreeSequenceAdjoinEdge
                  (ett.series.data.tree oldIdx.castSucc) f seed) := by
          rcases seedRoute with hPE | hSER
          · left
            exact ⟨kindEq.symm.trans hPE.1, hPE.2.trans treeEq⟩
          · right
            rcases hSER with ⟨hk, f, he, hs⟩
            refine ⟨?_, f, ?_, ?_⟩
            · rcases hk with hk | hk
              · exact Or.inl (kindEq.symm.trans hk)
              · exact Or.inr (kindEq.symm.trans hk)
            · exact edgesEq.symm.trans he
            · rw [← treeEq]
              exact hs
        have bound := hold i hi hiold pi seed candidate proper one stableOld
          routeOld closure
        rw [nextEq]
        simpa [newNext, oldNext] using bound
      · have hlast' : i < ett.rounds + 1 := by
          simpa using hlast
        have hieq : i = ett.rounds := by omega
        subst i
        let oldIdx : Fin (ett.rounds + 1) := Fin.last ett.rounds
        let newIdx : Fin ((ett.rounds + 1) + 1) := ⟨ett.rounds, by omega⟩
        let oldNext : Fin (ett.rounds + 2) := Fin.last (ett.rounds + 1)
        let newNext : Fin ((ett.rounds + 1) + 2) :=
          ⟨ett.rounds + 1, by omega⟩
        have indexEq : newIdx = oldIdx.castSucc := by ext; rfl
        have treeIndexEq : newIdx.castSucc = oldIdx.castSucc.castSucc := by
          rw [indexEq]
        have nextIndexEq : newNext = oldNext.castSucc := by ext; rfl
        have treeEq : extended.data.tree newIdx.castSucc =
            ett.series.data.tree oldIdx.castSucc := by
          rw [happend, treeIndexEq]
          simp [TashkinovSeriesDataAppend]
        have coloringEq : extended.data.coloring newIdx =
            ett.series.data.coloring oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have kindEq : extended.data.kind newIdx = ett.series.data.kind oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have edgesEq : extended.data.connectingEdges newIdx =
            ett.series.data.connectingEdges oldIdx := by
          rw [happend, indexEq]
          simp [TashkinovSeriesDataAppend]
        have storedEq : TashkinovStoredColors extended.data newIdx =
            TashkinovStoredColors ett.series.data oldIdx := by
          rw [happend, indexEq]
          have h := TashkinovStoredColorsAppend ett.series.data newTree newColoring
            newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
            newDelta newGamma oldIdx
          exact h
        have nextEq : extended.data.tree newNext = ett.series.data.tree oldNext := by
          rw [happend, nextIndexEq]
          simp [TashkinovSeriesDataAppend]
        have stableOld : StableColoring (ett.series.data.tree oldIdx.castSucc)
            (TashkinovStoredColors ett.series.data oldIdx)
            (ett.series.data.coloring oldIdx) pi := by
          rw [← treeEq, ← storedEq, ← coloringEq]
          simpa [newIdx] using stable
        have routeOld :
            (ett.series.data.kind oldIdx = some TashkinovExtensionKind.PE /\
              seed = ett.series.data.tree oldIdx.castSucc) \/
            ((ett.series.data.kind oldIdx = some TashkinovExtensionKind.SE \/
                ett.series.data.kind oldIdx = some TashkinovExtensionKind.RE) /\
              exists f : E, ett.series.data.connectingEdges oldIdx = {f} /\
                TreeSequenceAdjoinEdge
                  (ett.series.data.tree oldIdx.castSucc) f seed) := by
          rcases seedRoute with hPE | hSER
          · left
            exact ⟨kindEq.symm.trans hPE.1, hPE.2.trans treeEq⟩
          · right
            rcases hSER with ⟨hk, f, he, hs⟩
            refine ⟨?_, f, ?_, ?_⟩
            · rcases hk with hk | hk
              · exact Or.inl (kindEq.symm.trans hk)
              · exact Or.inr (kindEq.symm.trans hk)
            · exact edgesEq.symm.trans he
            · rw [← treeEq]
              exact hs
        have bound := hterminal pi seed candidate proper one stableOld routeOld closure
        rw [nextEq]
        simpa [newNext, oldNext] using bound

end GoldbergSeymour

end
