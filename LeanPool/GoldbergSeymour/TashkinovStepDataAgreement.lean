/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataPrefix
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsAppend
public import LeanPool.GoldbergSeymour.TashkinovStoredColorsPrefix

/-!
# Agreement of series-step data

Shared transports extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The case-independent data used by one noninitial series step agree at two indices. -/
structure TashkinovStepDataAgreement {V E : Type*} [Fintype E] {G : LooplessMultigraph V E}
    {k rounds targetRounds : ℕ} {e0 : E}
    (source : TashkinovSeriesData G k rounds e0)
    (target : TashkinovSeriesData G k targetRounds e0)
    (i : Fin rounds) (j : Fin targetRounds) : Prop where
  previousColoring : target.coloring j.castSucc = source.coloring i.castSucc
  previousTree : target.tree j.succ.castSucc = source.tree i.succ.castSucc
  currentTree : target.tree j.castSucc.succ = source.tree i.castSucc.succ
  currentColoring : target.coloring j.succ = source.coloring i.succ
  currentStored : target.stored j.succ = source.stored i.succ
  currentEdges : target.connectingEdges j.succ = source.connectingEdges i.succ
  currentKind : target.kind j.succ = source.kind i.succ
  currentVertex : target.chosenVertex j.succ = source.chosenVertex i.succ
  currentOutside : target.outsideVertex j.succ = source.outsideVertex i.succ
  currentDelta : target.delta j.succ = source.delta i.succ
  currentGamma : target.gamma j.succ = source.gamma i.succ
  outputTree : target.tree j.succ.succ = source.tree i.succ.succ
  storedColors : TashkinovStoredColors target j.castSucc = TashkinovStoredColors source i.castSucc

/-- Appending a round preserves the full data of every earlier noninitial step. -/
theorem TashkinovStepDataAgreement.append {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E}
    {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0) (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind) (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k)) (i : Fin rounds) :
    TashkinovStepDataAgreement data
      (TashkinovSeriesDataAppend data newTree newColoring newStored newConnectingEdges
        newKind newChosenVertex newOutsideVertex newDelta newGamma) i i.castSucc := by
  constructor
  · simp only [TashkinovSeriesDataAppend, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · simp only [TashkinovSeriesDataAppend, Fin.succ_castSucc, Fin.lastCases_castSucc]
  · exact TashkinovStoredColorsAppend data newTree newColoring newStored newConnectingEdges
      newKind newChosenVertex newOutsideVertex newDelta newGamma i.castSucc

/-- Taking a prefix preserves the full data of each retained noninitial step. -/
theorem TashkinovStepDataAgreement.prefix {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E}
    {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0)
    (m : ℕ) (hm : m ≤ rounds) (i : Fin rounds) (hi : i.val < m) :
    TashkinovStepDataAgreement data (TashkinovSeriesDataPrefix m hm data) i ⟨i.val, hi⟩ := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact TashkinovStoredColorsPrefix m hm data (⟨i.val, hi⟩ : Fin m).castSucc

end GoldbergSeymour

end
