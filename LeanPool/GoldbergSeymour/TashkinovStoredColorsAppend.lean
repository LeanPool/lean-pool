/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import LeanPool.GoldbergSeymour.TashkinovStoredColors

/-!
# Tashkinov Stored Colors Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovStoredColorsAppend {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (i : Fin (rounds + 1)) :
    TashkinovStoredColors
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      i.castSucc = TashkinovStoredColors data i := by
  classical
  let _ := Fintype.ofFinite V
  unfold TashkinovStoredColors
  simp only [Fin.val_castSucc]
  split_ifs with hi
  · rfl
  · apply Finset.ext
    intro c
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    constructor
    · rintro ⟨hc, hmissing⟩
      rw [Finset.mem_biUnion] at hc
      rcases hc with ⟨h, -, hc⟩
      have hle : h.val ≤ i.val := by
        by_contra hn
        simp [hn] at hc
      simp only [hle, ↓reduceIte] at hc
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      have hcOld : c ∈ data.stored oldH := by
        rw [hEq] at hc
        simpa [TashkinovSeriesDataAppend] using hc
      have oldHle : oldH.val ≤ i.val := hle
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_biUnion]
        refine ⟨oldH, Finset.mem_univ _, ?_⟩
        simp only [ite_eq_left oldHle]
        exact hcOld
      · simpa [TashkinovSeriesDataAppend] using hmissing
    · rintro ⟨hc, hmissing⟩
      rw [Finset.mem_biUnion] at hc
      rcases hc with ⟨h, -, hc⟩
      have hle : h.val ≤ i.val := by
        by_contra hn
        simp [hn] at hc
      simp [hle] at hc
      have hleCast : h.castSucc.val ≤ i.val := hle
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_biUnion]
        refine ⟨h.castSucc, Finset.mem_univ _, ?_⟩
        simp only [ite_eq_left hleCast]
        simpa [TashkinovSeriesDataAppend] using hc
      · simpa [TashkinovSeriesDataAppend] using hmissing

end GoldbergSeymour

end
