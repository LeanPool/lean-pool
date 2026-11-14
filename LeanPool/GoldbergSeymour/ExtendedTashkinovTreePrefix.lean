/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesFinalETTExists
public import LeanPool.GoldbergSeymour.TashkinovSeriesPrefix

/-!
# Extended Tashkinov Tree Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtendedTashkinovTreePrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (m : ℕ) (hmPositive : 1 ≤ m) (hmBefore : m < ett.rounds)
    (terminalIndex : Fin (ett.rounds + 2))
    (hterminal : terminalIndex.val = m + 1)
    (generatingIndex : Fin (ett.rounds + 1))
    (hgenerating : generatingIndex.val = m) :
    ∃ restricted : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree terminalIndex)
        (ett.series.data.coloring generatingIndex),
      ∃ hr : restricted.rounds = m,
        (∀ i : Fin (restricted.rounds + 2),
          restricted.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i)) ∧
        (∀ i : Fin (restricted.rounds + 1),
          restricted.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          restricted.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          restricted.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          restricted.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          restricted.series.data.chosenVertex i =
              ett.series.data.chosenVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.outsideVertex i =
              ett.series.data.outsideVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.delta i =
              ett.series.data.delta (Fin.castLE (by omega) i) ∧
          restricted.series.data.gamma i =
              ett.series.data.gamma (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors restricted.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i) ∧
          HEq (restricted.series.certified i)
            (ett.series.certified (Fin.castLE (by omega) i))) := by
  classical
  obtain ⟨restrictedSeries, hdata, hcert⟩ :=
    TashkinovSeriesPrefix G k ett.rounds e0 input ett.series m (by omega)
  have htreeDisplay :
      restrictedSeries.data.tree (Fin.last (m + 1)) =
        ett.series.data.tree terminalIndex := by
    rw [hdata]
    simp only [TashkinovSeriesDataPrefix]
    congr 1
    apply Fin.ext
    simpa using hterminal.symm
  have hcolorDisplay :
      restrictedSeries.data.coloring (Fin.last m) =
        ett.series.data.coloring generatingIndex := by
    rw [hdata]
    simp only [TashkinovSeriesDataPrefix]
    congr 1
    apply Fin.ext
    simpa using hgenerating.symm
  have hfinal := TashkinovSeriesFinalETTExists G k m e0 input
    restrictedSeries (by omega)
  rw [htreeDisplay, hcolorDisplay] at hfinal
  obtain ⟨restricted, hr, hseries⟩ := hfinal
  cases hr
  have hseriesEq : restricted.series = restrictedSeries :=
    eq_of_heq hseries
  cases hseriesEq
  refine ⟨restricted, rfl, ?_, ?_⟩
  · intro i
    rw [hdata]
    rfl
  · intro i
    have hcolor := congrArg (fun d => d.coloring i) hdata
    have hstored := congrArg (fun d => d.stored i) hdata
    have hedges := congrArg (fun d => d.connectingEdges i) hdata
    have hkind := congrArg (fun d => d.kind i) hdata
    have hchosen := congrArg (fun d => d.chosenVertex i) hdata
    have houtside := congrArg (fun d => d.outsideVertex i) hdata
    have hdelta := congrArg (fun d => d.delta i) hdata
    have hgamma := congrArg (fun d => d.gamma i) hdata
    simp only [TashkinovSeriesDataPrefix] at hcolor hstored hedges hkind hchosen
    have houtside' : restricted.series.data.outsideVertex i =
        ett.series.data.outsideVertex (Fin.castLE (by omega) i) := by
      simpa only [TashkinovSeriesDataPrefix] using houtside
    have hdelta' : restricted.series.data.delta i =
        ett.series.data.delta (Fin.castLE (by omega) i) := by
      simpa only [TashkinovSeriesDataPrefix] using hdelta
    have hgamma' : restricted.series.data.gamma i =
        ett.series.data.gamma (Fin.castLE (by omega) i) := by
      simpa only [TashkinovSeriesDataPrefix] using hgamma
    refine ⟨hcolor, hstored, hedges, hkind, hchosen, houtside', hdelta',
      hgamma', ?_, hcert i⟩
    rw [hdata]
    exact TashkinovStoredColorsPrefix restricted.rounds (by omega)
      ett.series.data i

end GoldbergSeymour

end
