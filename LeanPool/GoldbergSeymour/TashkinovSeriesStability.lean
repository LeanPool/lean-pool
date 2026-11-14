/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.StableColoring

/-!
# Stability reconstructed from series prefixes

General data-level facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Casting an appended coloring row preserves every coloring of its prefix. -/
theorem TashkinovSeriesData.prefixColoringOfCast {E : Type*} {k rounds shorter : ℕ}
    (roundsEqual : shorter + 1 = rounds)
    (earlierData : Fin (shorter + 1) → PartialEdgeColoring E k)
    (last : PartialEdgeColoring E k)
    (colorings : Fin (rounds + 1) → PartialEdgeColoring E k)
    (castColorings : ∀ i, colorings i =
      (Fin.lastCases last earlierData : Fin (shorter + 2) → PartialEdgeColoring E k)
        (Fin.cast (congrArg (fun n => n + 1) roundsEqual.symm) i))
    (i : Fin (shorter + 1)) :
    colorings (Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) i) = earlierData i := by
  rw [castColorings]
  have indexEqual :
      Fin.cast (congrArg (fun n => n + 1) roundsEqual.symm)
        (Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) i) = i.castSucc := Fin.ext rfl
  rw [indexEqual]
  exact Fin.lastCases_castSucc i

/-- Stability on a prefix and on the final stage gives stability on the full series data. -/
theorem TashkinovSeriesData.stabilityOfPrefix {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k rounds shorter : ℕ} {e0 : E}
    (original : TashkinovSeriesData G k rounds e0)
    (colorings : Fin (rounds + 1) → PartialEdgeColoring E k)
    (earlierData : TashkinovSeriesData G k shorter e0)
    (replacement : Fin (shorter + 1) → PartialEdgeColoring E k)
    (roundsEqual : shorter + 1 = rounds)
    (trees : ∀ i, earlierData.tree i =
      original.tree (Fin.castLE (by omega : shorter + 2 ≤ rounds + 2) i))
    (stored : ∀ i, TashkinovStoredColors earlierData i =
      TashkinovStoredColors original (Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) i))
    (oldColorings : ∀ i, earlierData.coloring i =
      original.coloring (Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) i))
    (newColorings : ∀ i, colorings (Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) i) =
      replacement i)
    (prefixStable : ∀ i : Fin shorter,
      StableColoring (earlierData.tree i.succ.castSucc) (TashkinovStoredColors earlierData i.succ)
        (earlierData.coloring i.succ) (replacement i.succ))
    (lastStable : StableColoring (original.tree (Fin.last rounds).castSucc)
      (TashkinovStoredColors original (Fin.last rounds))
      (original.coloring (Fin.last rounds)) (colorings (Fin.last rounds)))
    (i : Fin rounds) :
    StableColoring (original.tree i.succ.castSucc) (TashkinovStoredColors original i.succ)
      (original.coloring i.succ) (colorings i.succ) := by
  by_cases earlier : i.val < shorter
  · let j : Fin shorter := ⟨i.val, earlier⟩
    have indexEqual : Fin.castLE (by omega : shorter + 1 ≤ rounds + 1) j.succ = i.succ :=
      Fin.ext rfl
    have treeIndexEqual :
        Fin.castLE (by omega : shorter + 2 ≤ rounds + 2) j.succ.castSucc = i.succ.castSucc :=
      Fin.ext rfl
    have stable := prefixStable j
    rw [trees j.succ.castSucc, stored j.succ, oldColorings j.succ] at stable
    have newColoring : colorings i.succ = replacement j.succ := by
      simpa only [indexEqual] using newColorings j.succ
    rw [newColoring]
    simpa only [indexEqual, treeIndexEqual] using stable
  · have last : i.succ = Fin.last rounds := Fin.ext (by have := i.isLt; simp; omega)
    rw [last]
    exact lastStable

/-- A one-round series only needs its terminal stability fact. -/
theorem TashkinovSeriesData.stabilityOfOneRound {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (original : TashkinovSeriesData G k rounds e0)
    (colorings : Fin (rounds + 1) → PartialEdgeColoring E k)
    (oneRound : rounds = 1)
    (lastStable : StableColoring (original.tree (Fin.last rounds).castSucc)
      (TashkinovStoredColors original (Fin.last rounds))
      (original.coloring (Fin.last rounds)) (colorings (Fin.last rounds)))
    (i : Fin rounds) :
    StableColoring (original.tree i.succ.castSucc) (TashkinovStoredColors original i.succ)
      (original.coloring i.succ) (colorings i.succ) := by
  have last : i.succ = Fin.last rounds := Fin.ext (by have := i.isLt; simp; omega)
  rw [last]
  exact lastStable

end GoldbergSeymour

end
